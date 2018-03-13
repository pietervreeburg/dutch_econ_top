# Mergingtool made for Dutch Economists top 2016
# Author: Pieter Vreeburg, vreeburg@ese.eur.nl

# DATE MODIFIED: 2017_11_16

# issues
    # matching general:
        # fuzzy matching on lastname token: bastuerk, nalan -> basturk, nalan / menkveldc, albert j -> menkveld, albert j: add to pass 4
            # Add maybe extra checks like in pass 3? (luckily these misspelled names often have only 1 publ attached)
        # optimise pass 4, merge names if:
            # even if there is no overlap between first_nl_places, but
            # there is only 1 matching possibility in the whole dataset (bettendorf, l -> bettendorf, leon, bosker, e m -> bosker, maarten, bijvank, m -> bijvank, marco)
    # matching specific:
        # redekop ken -> redekop william k: will not be matched in pass 3 due to too little similarity between 'ken' and 'k'. 'Ken' is too long for use in pass 4 due to len token > 1)
        # de jong, ph r -> de jong philip: the same person, but not matched in pass 4 due to len second token > 1
        # herings, p jean jacques -> herings, p jeanjacques: the same person, but not matched in pass 4 due to third token > 1
        # de koster m b m -> de koster, rene b m: the same person, but this is not picked up by any passes (luckily only 1 publ on de koster, m b m)
        # pieters, f m g rik = pieters, rik: the same person, but this is not picked up by any passes
        # van der ploeg, rick -> van der ploeg, frederick: not merged even though they are obviously the same person
        # duva, teresa bago / bago duva, theresa / d uva, teresa bago: tough name to handle

    # performance:
        # increase performance with a dict lookup for a smaller set of records to examine. In the current implementation everything is examined continuously

# imports
import os # for os level functions, from std library
import json # to import / export json, from std library
import re # for regular expressions, from std library
from datetime import datetime # for dates + times, from std. library

from fuzzywuzzy import fuzz # fuzzy string matching, from PyPI
import Levenshtein # Levenshtein distances for fuzzywuzzy, from PyPI

# settings vars
INPUTPATH = r'\\campus.eur.nl\shared\departments\ESE-FD-BB-ONDERZOEK\Economen_tops\Economen Top 40 2017'
INPUTFILE = 'WoS_concat_econ_top_2017.txt' # production file

# functions
def merge_pass(input_dict, output_dict, blacklist, merge_rule):
    for author_name_1, author_values_1 in input_dict.items():
        if author_name_1 in blacklist: # author has been blacklisted, continue
            continue
        author_compare_1 = (author_values_1['tokenized_name'], author_name_1)
        for author_name_2, author_values_2 in input_dict.items():
            if author_name_1 == author_name_2: # same author, continue
                continue
            if author_name_2 in blacklist: # author has been blacklisted, continue
                continue
            author_compare_2 = (author_values_2['tokenized_name'], author_name_2)
            # determine author with the longest tokenized name (shorter names are merged into the longer name)
            # if equal length (van exel job - van exel n j a): author with the least tokens is considered as author with the longest tokenized name
            if len(''.join(author_compare_1[0])) != len(''.join(author_compare_2[0])):
                author_compare_short, author_compare_long = sorted([author_compare_1,
                                                                    author_compare_2],
                                                                    key = lambda tokens: len(''.join(tokens[0])))
            else:
                author_compare_short, author_compare_long = sorted([author_compare_1,
                                                                    author_compare_2],
                                                                    key = lambda tokens: len(tokens[0]), reverse = True)
            # exclusion rules for better performance or more conservative matching
            if merge_rule == 1 or merge_rule == 2:
                if len(author_compare_1[0]) < 3: # author outer loop has < 3 tokens, break comparison loop
                    break
                if len(author_compare_2[0]) < 3 or len(author_compare_1[0]) != len(author_compare_2[0]): # author comparison loop has < 3 tokens or unequal number of tokens,
                                                                                                         # next iteration comparison loop
                    continue
            if merge_rule == 3:
                if len(author_compare_long[0]) < 3 or len(author_compare_short[0][1]) < 2:  # author_compare_long has < 3 tokens or length 2nd token of author_compare_short < 2
                                                                                            # next iteration comparison loop
                    continue
            if merge_rule == 4:
                # for more conservative matching, only consider author_compare_short if the 2nd and further tokens are max 1 char per token
                if len(''.join(author_compare_short[0][1:])) > len(author_compare_short[0][1:]):
                    continue
            # print 'compare...', author_compare_short[1], 'with...', author_compare_long[1] # for debugging
            # merge_rule_1
            # the tokens of the shorter tokenized name (with at least 3 tokens) match
            # the first token, the second token and the first char of all subsequent tokens of the longer tokenized name (with at least 3 tokens)
            # vreeburg pieter f -> vreeburg pieter frederik
            if merge_rule == 1:
                if author_compare_short[0][:2] == author_compare_long[0][:2]: # compare first 2 tokens
                    for token_index, token_value in enumerate(author_compare_short[0][2:]): # compare first char of 3rd and further tokens
                        if token_value[0] != author_compare_long[0][token_index + 2][0]:
                            break
                    else:
                        merge_items(author_compare_short, author_compare_long, author_dict, author_dict_merged)
                        blacklist.append(author_compare_short[1])
                        break
            # merge rule 2
            # the first token of the shorter tokenized name (with at least 3 tokens) matches the first token of the longer tokenized name (with at least 3 tokens)
            # and the first char of all subsequent tokens of the longer tokenized name matches
            # the first char of all subsequent tokens of the shorter tokenized name
            # vreeburg, p f -> vreeburg pieter frederik
            # redekop, w ken -> redekop, william k
            # born, manse ph -> born, marise ph
            if merge_rule == 2:
                if author_compare_short[0][0] == author_compare_long[0][0]: # compare first tokens
                    for token_index, token_value in enumerate(author_compare_short[0][1:]): # compare first chars of 2nd and further tokens
                        if token_value[0] != author_compare_long[0][token_index + 1][0]:
                            break
                    else:
                        merge_items(author_compare_short, author_compare_long, author_dict, author_dict_merged)
                        blacklist.append(author_compare_short[1])
                        break
            # merge rule 3
            # the first token of the shorter tokenized name matches the first token of the longer tokenized name (with at least 3 tokens)
            # and the second token (len > 1) of the shorter tokenized name (fuzzy) matches the second OR the third token of the longer tokenized name
            # vreeburg pieter -> vreeburg pieter frederik
            # bovenberg lans -> bovenberg a lans
            if merge_rule == 3:
                if author_compare_short[0][0] == author_compare_long[0][0] and \
                        (fuzz.ratio(author_compare_short[0][1], author_compare_long[0][1]) > 90
                            or fuzz.ratio(author_compare_short[0][1], author_compare_long[0][2]) > 90):
                    # extra check for any intersection of first_nl_places of both authors
                    if len(set(author_dict[author_compare_short[1]]['first_nl_places']) & set(author_dict[author_compare_long[1]]['first_nl_places'])) > 0:
                        merge_items(author_compare_short, author_compare_long, author_dict, author_dict_merged)
                        blacklist.append(author_compare_short[1])
                        break
            # merge rule 4
            # the first token and the second token OR the third token of the shorter tokenized name match
            # the first token and the first char of the second token of longer tokenized name (guard for shorter tokenized names with only 2 tokens)
            # vreeburg p -> vreeburg pieter frederik
            # van nierop j e m -> van nierop erjen
            # van den akker j m -> van den akker marjan
            # van exel, n j a -> van exel job
            # van beers, w c m -> van beers cees (no place intersection)
            # bosker e m -> bosker maarten (no place intersection)
            if merge_rule == 4:
                if author_compare_short[0][0] == author_compare_long[0][0]:
                    if author_compare_short[0][1] != author_compare_long[0][1][0]:
                        if len(author_compare_short[0]) > 2:
                            if author_compare_short[0][2] != author_compare_long[0][1][0]:
                                continue
                        else:
                            continue
                    # extra check for any intersection of first_nl_places of both authors
                    if len(set(author_dict[author_compare_short[1]]['first_nl_places']) & set(author_dict[author_compare_long[1]]['first_nl_places'])) > 0:
                        merge_items(author_compare_short, author_compare_long, author_dict, author_dict_merged)
                        blacklist.append(author_compare_short[1])
                        break

    # print blacklist # for debugging
    return blacklist

def merge_items(author_compare_short, author_compare_long, author_dict, author_dict_merged):
    print 'merge...', author_compare_short[1], 'with...', author_compare_long[1] # for debugging
    author_dict_merged.setdefault(author_compare_long[1], author_dict[author_compare_long[1]]) # add author with longest tokenized name to author_dict_merged
    author_dict_merged[author_compare_long[1]].setdefault('merged_names', [])
    author_dict_merged[author_compare_long[1]]['merged_names'].append(author_compare_short[1])
    for key, lst in author_dict[author_compare_short[1]].items(): # add first_nl_places and wos_ids to author_dict_merged
        if key == 'tokenized_name' or key == 'dutch':
            continue
        for item in lst:
            if item not in author_dict_merged.get(author_compare_long[1]).get(key):
                author_dict_merged[author_compare_long[1]][key].append(item)

def write_json_file(dict, writefile):
    outfile = open(writefile + '.txt', 'w')
    json.dump(dict, outfile, indent = 4)

# main
start_time = datetime.now()
print 'Build initial author dict'
author_dict = {}
author_dict_merged = {}
institute_dict = {}
institute_dict_unique = {}
blacklist = []
file = open(os.path.join(INPUTPATH, INPUTFILE)).read().splitlines()
line_num = 0

lookup_institutes = {
    'EUR' : 'rotterdam',
    'UvT' : 'tilburg',
    'UM' : 'maastricht',
    'RUG' : 'groningen',
    'UU' : 'utrecht',
    'RUN' : 'nijmegen'
    }

# parse input file to author_dict
for line in file:
    line_num += 1
    if line.strip() == '': # skip empty lines
        continue
    # print line_num # for debugging
    line_split = line.split('\t')
    authors_full = line_split[5].lower() # field tag AF
    author_list = [author.strip() for author in authors_full.split(';')]
    affs = line_split[22].lower() # field tag C1
    affs = re.sub(r'[^a-z, ;\[\]]', '', affs) # remove punctuation, except commas, spaces, ; and [] in affs
    # publ_year = line_split[44] # field tag PY
    wos_id = line_split[-7] # field tag UT
    for author_name in author_list:
        # find list of individual author's affiliations, check for dutch affiliation and find first NL place
        author_name = re.sub(r'[^a-z, ]', '', author_name) # remove punctuation, except commas and spaces in author_name
        aff = re.findall(author_name + r'.*?](.+?)(?:;|$)', affs)
        dutch = None
        first_nl_place = None
        if aff:
            aff = '; '.join(aff).strip()
            if aff.find('netherland') >= 0:
                dutch = True
                first_nl_place = re.findall(r'(\w+), netherland', aff)
                if first_nl_place:
                    first_nl_place = first_nl_place[0]
        # [INSTITUTE_TOP, PART 1]
        if dutch:
            author_institutes = {}
            for institute_name, institute_place in lookup_institutes.items():
                text_position = aff.find(institute_place)
                if text_position >= 0:
                    author_institutes[institute_name] = text_position
            # specific search patterns for UvA and VU in Amsterdam
            if aff.find('univ amsterdam') >= 0 and aff.find('vrije univ amsterdam') == -1 and aff.find('vu') == -1:
                text_position = aff.find('amsterdam')
                author_institutes['UvA'] = text_position
            elif aff.find('vrije univ amsterdam') >= 0:
                text_position = aff.find('vrije univ amsterdam')
                author_institutes['VU'] = text_position
            elif aff.find('vu') >= 0:
                text_position = aff.find('vu')
                author_institutes['VU'] = text_position
            if len(author_institutes) > 0:
                primary_institute = min(author_institutes, key = author_institutes.get)
                institute_dict.setdefault(primary_institute, []).append(wos_id)
        # tokenize author_name
        author_nametokens = []
        try:
            author_lastname, author_firstname = author_name.split(',', 1)
        except ValueError:
            try:
                author_lastname, author_firstname = author_name.split(' ', 1)
            except ValueError:
                # print 'author_name not splitable:', author_name
                continue # author_name cannot be split with enough precision, ignore author and continue with next author
        author_nametokens.append(author_lastname.strip())
        for token in author_firstname.strip().split(' '):
            author_nametokens.append(token)
        if len(author_nametokens) < 2:
            # print 'author_name not enough tokens:', author_name
            continue # authors with a last name only cannot be used for merging, ignore author and continue with next author
        # store in author_dict
        author_dict.setdefault(author_name, {'tokenized_name' : author_nametokens, 'dutch': False, 'publications' : [], 'first_nl_places': []})
        if dutch:
            author_dict[author_name]['dutch'] = dutch
        if first_nl_place <> None and first_nl_place not in author_dict[author_name]['first_nl_places']:
            author_dict[author_name]['first_nl_places'].append(first_nl_place)
        if wos_id not in author_dict[author_name]['publications']:
            author_dict[author_name]['publications'].append(wos_id)

# [INSTITUTE_TOP, PART 2] make publication lists in institute_dict unique
for key, values in institute_dict.items():
    institute_dict_unique[key] = set(values)

print 'Total author_dict:', len(author_dict)
# print author_dict to file, for debugging
write_json_file(author_dict, os.path.join(INPUTPATH, 'PARSED_FILE_' + INPUTFILE[:-4]))

# filter only Dutch authors to author_dict_filtered
# filter after processing all records to ensure the full corpus of authors with at least 1 Dutch publication is included in the resulting dataset
author_dict_filtered = {}
for author_name, author_values in author_dict.items():
    if author_values['dutch'] == True:
        author_dict_filtered[author_name] = author_values

print 'Total author_dict_filtered:', len(author_dict_filtered)
# print author_dict_filtered to file, for debugging
write_json_file(author_dict_filtered, os.path.join(INPUTPATH, 'FILTERED_FILE_' + INPUTFILE[:-4]))

# merge authors
print 'merge: 1st pass'
merge_pass(author_dict_filtered, author_dict_merged, blacklist, 1)
print 'merge: 2nd pass'
merge_pass(author_dict_filtered, author_dict_merged, blacklist, 2)
print 'merge: 3rd pass'
merge_pass(author_dict_filtered, author_dict_merged, blacklist, 3)
print 'merge: 4th pass'
merge_pass(author_dict_filtered, author_dict_merged, blacklist, 4)
# add unmerged autors
print 'merge: final pass'
for author_name, author_values in author_dict_filtered.items():
    if author_name in blacklist or author_name in author_dict_merged:
        continue
    else:
        author_dict_merged[author_name] = author_values

# print author_dict_merged to file, for debugging
write_json_file(author_dict_merged, os.path.join(INPUTPATH, 'MERGED_FILE_' + INPUTFILE[:-4]))

# print list of author_dict_merged with merged_names, to check
print_list = []
for author, author_values in author_dict_merged.items():
    merged_names = author_values.get('merged_names')
    if merged_names:
        author = author + ';' + str.join(' / ', merged_names)
    print_list.append(author)
print_list = sorted(print_list)
with open(os.path.join(INPUTPATH, 'LIST_MERGED_DICT_' + INPUTFILE[:-4] + '.txt'), 'w') as f_out:
    for item in print_list:
        item = item + '\n'
        f_out.write(item)

# print author_dict_merged to file for import in access
with open(os.path.join(INPUTPATH, 'ACCESS_IMPORT_AUTHORS_' + INPUTFILE[:-4] + '.txt'), 'w') as f_out:
    for author, author_values in author_dict_merged.items():
        for wos_id in author_values['publications']:
            line = author + ';' + wos_id + '\n'
            f_out.write(line)

# [INSTITUTE_TOP, PART 3], print institute_dict_unique to file for import in access
with open(os.path.join(INPUTPATH, 'ACCESS_IMPORT_INSTITUTES_' + INPUTFILE[:-4] + '.txt'), 'w') as f_out:
    for institute, institute_values in institute_dict_unique.items():
        for wos_id in institute_values:
            line = institute + ';' + wos_id + '\n'
            f_out.write(line)

end_time = datetime.now()
print 'Done, elapsed time:', str(end_time - start_time).split('.')[0]