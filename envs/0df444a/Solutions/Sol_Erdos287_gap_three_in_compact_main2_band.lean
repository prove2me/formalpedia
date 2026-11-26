-- Prove2me | solution 1 for Erdos287.gap_three_in_compact_main2_band
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T10:43:58.905213+00:00
-- url     : https://prove2.me/submissions/3aa41899-657d-4b43-858e-7571b66fd3a9

import Mathlib
import Theorems.Thm_Erdos287_factorial_prime_rung

/- Rung data from Reza Ramji's erdos-287-lean, commit
2b2ecb1022cc3bfe249d9733003d3488f2d3027f. The proof terms are rebuilt
using compact Lucas witnesses and the Prove2Me factorial rung lemma. -/

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

private theorem prime_from_two_factors (n p a g : ℕ) (hp : p.Prime) (hfactor : n - 1 = p * 2 ^ a)
    (hfull : (g : ZMod n) ^ (n - 1) = 1)
    (htwo : (g : ZMod n) ^ ((n - 1) / 2) ≠ 1)
    (hprime : (g : ZMod n) ^ ((n - 1) / p) ≠ 1) :
    n.Prime := by
  apply lucas_primality n (g : ZMod n) hfull
  intro r hr hdiv
  rw [hfactor] at hdiv
  rcases (Nat.Prime.dvd_mul hr).mp hdiv with h | h
  · have he : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).mp h
    simpa only [he] using hprime
  · have hd : r ∣ 2 := hr.dvd_of_dvd_pow h
    have he : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp hd
    simpa only [he] using htwo

private theorem prime0p : Nat.Prime 191305253 := by
  have hfactor : (191305253 : ℕ) - 1 = 47826313 * 2 ^ 2 := by
    norm_num
  refine prime_from_two_factors 191305253 47826313 2 2 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (191305253 : ℕ) - 1 = 191305252 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((191305253 : ℕ) - 1) / 2 = 95652626 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((191305253 : ℕ) - 1) / 47826313 = 4 by norm_num]
    reduce_mod_char <;> decide

private theorem prime0q : Nat.Prime 382610507 := by
  have hfactor : (382610507 : ℕ) - 1 = 191305253 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 382610507 191305253 1 2 prime0p hfactor ?_ ?_ ?_
  · rw [show (382610507 : ℕ) - 1 = 382610506 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((382610507 : ℕ) - 1) / 2 = 191305253 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((382610507 : ℕ) - 1) / 191305253 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime1p : Nat.Prime 382609229 := by
  have hfactor : (382609229 : ℕ) - 1 = 95652307 * 2 ^ 2 := by
    norm_num
  refine prime_from_two_factors 382609229 95652307 2 2 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (382609229 : ℕ) - 1 = 382609228 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((382609229 : ℕ) - 1) / 2 = 191304614 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((382609229 : ℕ) - 1) / 95652307 = 4 by norm_num]
    reduce_mod_char <;> decide

private theorem prime1q : Nat.Prime 765218459 := by
  have hfactor : (765218459 : ℕ) - 1 = 382609229 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 765218459 382609229 1 2 prime1p hfactor ?_ ?_ ?_
  · rw [show (765218459 : ℕ) - 1 = 765218458 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((765218459 : ℕ) - 1) / 2 = 382609229 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((765218459 : ℕ) - 1) / 382609229 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime2p : Nat.Prime 765204809 := by
  have hfactor : (765204809 : ℕ) - 1 = 95650601 * 2 ^ 3 := by
    norm_num
  refine prime_from_two_factors 765204809 95650601 3 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (765204809 : ℕ) - 1 = 765204808 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((765204809 : ℕ) - 1) / 2 = 382602404 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((765204809 : ℕ) - 1) / 95650601 = 8 by norm_num]
    reduce_mod_char <;> decide

private theorem prime2q : Nat.Prime 1530409619 := by
  have hfactor : (1530409619 : ℕ) - 1 = 765204809 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 1530409619 765204809 1 2 prime2p hfactor ?_ ?_ ?_
  · rw [show (1530409619 : ℕ) - 1 = 1530409618 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1530409619 : ℕ) - 1) / 2 = 765204809 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1530409619 : ℕ) - 1) / 765204809 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime3p : Nat.Prime 1530202769 := by
  have hfactor : (1530202769 : ℕ) - 1 = 95637673 * 2 ^ 4 := by
    norm_num
  refine prime_from_two_factors 1530202769 95637673 4 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (1530202769 : ℕ) - 1 = 1530202768 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1530202769 : ℕ) - 1) / 2 = 765101384 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1530202769 : ℕ) - 1) / 95637673 = 16 by norm_num]
    reduce_mod_char <;> decide

private theorem prime3q : Nat.Prime 3060405539 := by
  have hfactor : (3060405539 : ℕ) - 1 = 1530202769 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 3060405539 1530202769 1 2 prime3p hfactor ?_ ?_ ?_
  · rw [show (3060405539 : ℕ) - 1 = 3060405538 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((3060405539 : ℕ) - 1) / 2 = 1530202769 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((3060405539 : ℕ) - 1) / 1530202769 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime4p : Nat.Prime 3060338273 := by
  have hfactor : (3060338273 : ℕ) - 1 = 95635571 * 2 ^ 5 := by
    norm_num
  refine prime_from_two_factors 3060338273 95635571 5 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (3060338273 : ℕ) - 1 = 3060338272 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((3060338273 : ℕ) - 1) / 2 = 1530169136 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((3060338273 : ℕ) - 1) / 95635571 = 32 by norm_num]
    reduce_mod_char <;> decide

private theorem prime4q : Nat.Prime 6120676547 := by
  have hfactor : (6120676547 : ℕ) - 1 = 3060338273 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 6120676547 3060338273 1 2 prime4p hfactor ?_ ?_ ?_
  · rw [show (6120676547 : ℕ) - 1 = 6120676546 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((6120676547 : ℕ) - 1) / 2 = 3060338273 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((6120676547 : ℕ) - 1) / 3060338273 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime5p : Nat.Prime 6120480449 := by
  have hfactor : (6120480449 : ℕ) - 1 = 95632507 * 2 ^ 6 := by
    norm_num
  refine prime_from_two_factors 6120480449 95632507 6 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (6120480449 : ℕ) - 1 = 6120480448 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((6120480449 : ℕ) - 1) / 2 = 3060240224 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((6120480449 : ℕ) - 1) / 95632507 = 64 by norm_num]
    reduce_mod_char <;> decide

private theorem prime5q : Nat.Prime 12240960899 := by
  have hfactor : (12240960899 : ℕ) - 1 = 6120480449 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 12240960899 6120480449 1 2 prime5p hfactor ?_ ?_ ?_
  · rw [show (12240960899 : ℕ) - 1 = 12240960898 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((12240960899 : ℕ) - 1) / 2 = 6120480449 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((12240960899 : ℕ) - 1) / 6120480449 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime6p : Nat.Prime 12240717953 := by
  have hfactor : (12240717953 : ℕ) - 1 = 95630609 * 2 ^ 7 := by
    norm_num
  refine prime_from_two_factors 12240717953 95630609 7 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (12240717953 : ℕ) - 1 = 12240717952 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((12240717953 : ℕ) - 1) / 2 = 6120358976 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((12240717953 : ℕ) - 1) / 95630609 = 128 by norm_num]
    reduce_mod_char <;> decide

private theorem prime6q : Nat.Prime 24481435907 := by
  have hfactor : (24481435907 : ℕ) - 1 = 12240717953 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 24481435907 12240717953 1 2 prime6p hfactor ?_ ?_ ?_
  · rw [show (24481435907 : ℕ) - 1 = 24481435906 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((24481435907 : ℕ) - 1) / 2 = 12240717953 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((24481435907 : ℕ) - 1) / 12240717953 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime7p : Nat.Prime 24477759233 := by
  have hfactor : (24477759233 : ℕ) - 1 = 95616247 * 2 ^ 8 := by
    norm_num
  refine prime_from_two_factors 24477759233 95616247 8 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (24477759233 : ℕ) - 1 = 24477759232 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((24477759233 : ℕ) - 1) / 2 = 12238879616 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((24477759233 : ℕ) - 1) / 95616247 = 256 by norm_num]
    reduce_mod_char <;> decide

private theorem prime7q : Nat.Prime 48955518467 := by
  have hfactor : (48955518467 : ℕ) - 1 = 24477759233 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 48955518467 24477759233 1 2 prime7p hfactor ?_ ?_ ?_
  · rw [show (48955518467 : ℕ) - 1 = 48955518466 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((48955518467 : ℕ) - 1) / 2 = 24477759233 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((48955518467 : ℕ) - 1) / 24477759233 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime8p : Nat.Prime 48954439169 := by
  have hfactor : (48954439169 : ℕ) - 1 = 95614139 * 2 ^ 9 := by
    norm_num
  refine prime_from_two_factors 48954439169 95614139 9 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (48954439169 : ℕ) - 1 = 48954439168 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((48954439169 : ℕ) - 1) / 2 = 24477219584 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((48954439169 : ℕ) - 1) / 95614139 = 512 by norm_num]
    reduce_mod_char <;> decide

private theorem prime8q : Nat.Prime 97908878339 := by
  have hfactor : (97908878339 : ℕ) - 1 = 48954439169 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 97908878339 48954439169 1 2 prime8p hfactor ?_ ?_ ?_
  · rw [show (97908878339 : ℕ) - 1 = 97908878338 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((97908878339 : ℕ) - 1) / 2 = 48954439169 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((97908878339 : ℕ) - 1) / 48954439169 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime9p : Nat.Prime 97905445889 := by
  have hfactor : (97905445889 : ℕ) - 1 = 95610787 * 2 ^ 10 := by
    norm_num
  refine prime_from_two_factors 97905445889 95610787 10 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (97905445889 : ℕ) - 1 = 97905445888 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((97905445889 : ℕ) - 1) / 2 = 48952722944 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((97905445889 : ℕ) - 1) / 95610787 = 1024 by norm_num]
    reduce_mod_char <;> decide

private theorem prime9q : Nat.Prime 195810891779 := by
  have hfactor : (195810891779 : ℕ) - 1 = 97905445889 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 195810891779 97905445889 1 2 prime9p hfactor ?_ ?_ ?_
  · rw [show (195810891779 : ℕ) - 1 = 195810891778 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((195810891779 : ℕ) - 1) / 2 = 97905445889 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((195810891779 : ℕ) - 1) / 97905445889 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime10p : Nat.Prime 195810777089 := by
  have hfactor : (195810777089 : ℕ) - 1 = 95610731 * 2 ^ 11 := by
    norm_num
  refine prime_from_two_factors 195810777089 95610731 11 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (195810777089 : ℕ) - 1 = 195810777088 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((195810777089 : ℕ) - 1) / 2 = 97905388544 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((195810777089 : ℕ) - 1) / 95610731 = 2048 by norm_num]
    reduce_mod_char <;> decide

private theorem prime10q : Nat.Prime 391621554179 := by
  have hfactor : (391621554179 : ℕ) - 1 = 195810777089 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 391621554179 195810777089 1 2 prime10p hfactor ?_ ?_ ?_
  · rw [show (391621554179 : ℕ) - 1 = 391621554178 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((391621554179 : ℕ) - 1) / 2 = 195810777089 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((391621554179 : ℕ) - 1) / 195810777089 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime11p : Nat.Prime 391621292033 := by
  have hfactor : (391621292033 : ℕ) - 1 = 95610667 * 2 ^ 12 := by
    norm_num
  refine prime_from_two_factors 391621292033 95610667 12 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (391621292033 : ℕ) - 1 = 391621292032 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((391621292033 : ℕ) - 1) / 2 = 195810646016 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((391621292033 : ℕ) - 1) / 95610667 = 4096 by norm_num]
    reduce_mod_char <;> decide

private theorem prime11q : Nat.Prime 783242584067 := by
  have hfactor : (783242584067 : ℕ) - 1 = 391621292033 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 783242584067 391621292033 1 2 prime11p hfactor ?_ ?_ ?_
  · rw [show (783242584067 : ℕ) - 1 = 783242584066 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((783242584067 : ℕ) - 1) / 2 = 391621292033 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((783242584067 : ℕ) - 1) / 391621292033 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime12p : Nat.Prime 783230083073 := by
  have hfactor : (783230083073 : ℕ) - 1 = 95609141 * 2 ^ 13 := by
    norm_num
  refine prime_from_two_factors 783230083073 95609141 13 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (783230083073 : ℕ) - 1 = 783230083072 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((783230083073 : ℕ) - 1) / 2 = 391615041536 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((783230083073 : ℕ) - 1) / 95609141 = 8192 by norm_num]
    reduce_mod_char <;> decide

private theorem prime12q : Nat.Prime 1566460166147 := by
  have hfactor : (1566460166147 : ℕ) - 1 = 783230083073 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 1566460166147 783230083073 1 2 prime12p hfactor ?_ ?_ ?_
  · rw [show (1566460166147 : ℕ) - 1 = 1566460166146 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1566460166147 : ℕ) - 1) / 2 = 783230083073 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1566460166147 : ℕ) - 1) / 783230083073 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime13p : Nat.Prime 1566450368513 := by
  have hfactor : (1566450368513 : ℕ) - 1 = 95608543 * 2 ^ 14 := by
    norm_num
  refine prime_from_two_factors 1566450368513 95608543 14 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (1566450368513 : ℕ) - 1 = 1566450368512 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1566450368513 : ℕ) - 1) / 2 = 783225184256 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1566450368513 : ℕ) - 1) / 95608543 = 16384 by norm_num]
    reduce_mod_char <;> decide

private theorem prime13q : Nat.Prime 3132900737027 := by
  have hfactor : (3132900737027 : ℕ) - 1 = 1566450368513 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 3132900737027 1566450368513 1 2 prime13p hfactor ?_ ?_ ?_
  · rw [show (3132900737027 : ℕ) - 1 = 3132900737026 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((3132900737027 : ℕ) - 1) / 2 = 1566450368513 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((3132900737027 : ℕ) - 1) / 1566450368513 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime14p : Nat.Prime 3132868820993 := by
  have hfactor : (3132868820993 : ℕ) - 1 = 95607569 * 2 ^ 15 := by
    norm_num
  refine prime_from_two_factors 3132868820993 95607569 15 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (3132868820993 : ℕ) - 1 = 3132868820992 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((3132868820993 : ℕ) - 1) / 2 = 1566434410496 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((3132868820993 : ℕ) - 1) / 95607569 = 32768 by norm_num]
    reduce_mod_char <;> decide

private theorem prime14q : Nat.Prime 6265737641987 := by
  have hfactor : (6265737641987 : ℕ) - 1 = 3132868820993 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 6265737641987 3132868820993 1 2 prime14p hfactor ?_ ?_ ?_
  · rw [show (6265737641987 : ℕ) - 1 = 6265737641986 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((6265737641987 : ℕ) - 1) / 2 = 3132868820993 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((6265737641987 : ℕ) - 1) / 3132868820993 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime15p : Nat.Prime 6265541558273 := by
  have hfactor : (6265541558273 : ℕ) - 1 = 95604577 * 2 ^ 16 := by
    norm_num
  refine prime_from_two_factors 6265541558273 95604577 16 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (6265541558273 : ℕ) - 1 = 6265541558272 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((6265541558273 : ℕ) - 1) / 2 = 3132770779136 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((6265541558273 : ℕ) - 1) / 95604577 = 65536 by norm_num]
    reduce_mod_char <;> decide

private theorem prime15q : Nat.Prime 12531083116547 := by
  have hfactor : (12531083116547 : ℕ) - 1 = 6265541558273 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 12531083116547 6265541558273 1 2 prime15p hfactor ?_ ?_ ?_
  · rw [show (12531083116547 : ℕ) - 1 = 12531083116546 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((12531083116547 : ℕ) - 1) / 2 = 6265541558273 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((12531083116547 : ℕ) - 1) / 6265541558273 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime16p : Nat.Prime 12530417532929 := by
  have hfactor : (12530417532929 : ℕ) - 1 = 95599499 * 2 ^ 17 := by
    norm_num
  refine prime_from_two_factors 12530417532929 95599499 17 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (12530417532929 : ℕ) - 1 = 12530417532928 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((12530417532929 : ℕ) - 1) / 2 = 6265208766464 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((12530417532929 : ℕ) - 1) / 95599499 = 131072 by norm_num]
    reduce_mod_char <;> decide

private theorem prime16q : Nat.Prime 25060835065859 := by
  have hfactor : (25060835065859 : ℕ) - 1 = 12530417532929 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 25060835065859 12530417532929 1 2 prime16p hfactor ?_ ?_ ?_
  · rw [show (25060835065859 : ℕ) - 1 = 25060835065858 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((25060835065859 : ℕ) - 1) / 2 = 12530417532929 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((25060835065859 : ℕ) - 1) / 12530417532929 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime17p : Nat.Prime 25059107012609 := by
  have hfactor : (25059107012609 : ℕ) - 1 = 95592907 * 2 ^ 18 := by
    norm_num
  refine prime_from_two_factors 25059107012609 95592907 18 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (25059107012609 : ℕ) - 1 = 25059107012608 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((25059107012609 : ℕ) - 1) / 2 = 12529553506304 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((25059107012609 : ℕ) - 1) / 95592907 = 262144 by norm_num]
    reduce_mod_char <;> decide

private theorem prime17q : Nat.Prime 50118214025219 := by
  have hfactor : (50118214025219 : ℕ) - 1 = 25059107012609 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 50118214025219 25059107012609 1 2 prime17p hfactor ?_ ?_ ?_
  · rw [show (50118214025219 : ℕ) - 1 = 50118214025218 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((50118214025219 : ℕ) - 1) / 2 = 25059107012609 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((50118214025219 : ℕ) - 1) / 25059107012609 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime18p : Nat.Prime 50109669179393 := by
  have hfactor : (50109669179393 : ℕ) - 1 = 95576609 * 2 ^ 19 := by
    norm_num
  refine prime_from_two_factors 50109669179393 95576609 19 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (50109669179393 : ℕ) - 1 = 50109669179392 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((50109669179393 : ℕ) - 1) / 2 = 25054834589696 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((50109669179393 : ℕ) - 1) / 95576609 = 524288 by norm_num]
    reduce_mod_char <;> decide

private theorem prime18q : Nat.Prime 100219338358787 := by
  have hfactor : (100219338358787 : ℕ) - 1 = 50109669179393 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 100219338358787 50109669179393 1 2 prime18p hfactor ?_ ?_ ?_
  · rw [show (100219338358787 : ℕ) - 1 = 100219338358786 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((100219338358787 : ℕ) - 1) / 2 = 50109669179393 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((100219338358787 : ℕ) - 1) / 50109669179393 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime19p : Nat.Prime 100203649564673 := by
  have hfactor : (100203649564673 : ℕ) - 1 = 95561647 * 2 ^ 20 := by
    norm_num
  refine prime_from_two_factors 100203649564673 95561647 20 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (100203649564673 : ℕ) - 1 = 100203649564672 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((100203649564673 : ℕ) - 1) / 2 = 50101824782336 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((100203649564673 : ℕ) - 1) / 95561647 = 1048576 by norm_num]
    reduce_mod_char <;> decide

private theorem prime19q : Nat.Prime 200407299129347 := by
  have hfactor : (200407299129347 : ℕ) - 1 = 100203649564673 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 200407299129347 100203649564673 1 2 prime19p hfactor ?_ ?_ ?_
  · rw [show (200407299129347 : ℕ) - 1 = 200407299129346 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((200407299129347 : ℕ) - 1) / 2 = 100203649564673 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((200407299129347 : ℕ) - 1) / 100203649564673 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime20p : Nat.Prime 200401078976513 := by
  have hfactor : (200401078976513 : ℕ) - 1 = 95558681 * 2 ^ 21 := by
    norm_num
  refine prime_from_two_factors 200401078976513 95558681 21 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (200401078976513 : ℕ) - 1 = 200401078976512 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((200401078976513 : ℕ) - 1) / 2 = 100200539488256 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((200401078976513 : ℕ) - 1) / 95558681 = 2097152 by norm_num]
    reduce_mod_char <;> decide

private theorem prime20q : Nat.Prime 400802157953027 := by
  have hfactor : (400802157953027 : ℕ) - 1 = 200401078976513 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 400802157953027 200401078976513 1 2 prime20p hfactor ?_ ?_ ?_
  · rw [show (400802157953027 : ℕ) - 1 = 400802157953026 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((400802157953027 : ℕ) - 1) / 2 = 200401078976513 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((400802157953027 : ℕ) - 1) / 200401078976513 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime21p : Nat.Prime 400737616003073 := by
  have hfactor : (400737616003073 : ℕ) - 1 = 95543293 * 2 ^ 22 := by
    norm_num
  refine prime_from_two_factors 400737616003073 95543293 22 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (400737616003073 : ℕ) - 1 = 400737616003072 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((400737616003073 : ℕ) - 1) / 2 = 200368808001536 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((400737616003073 : ℕ) - 1) / 95543293 = 4194304 by norm_num]
    reduce_mod_char <;> decide

private theorem prime21q : Nat.Prime 801475232006147 := by
  have hfactor : (801475232006147 : ℕ) - 1 = 400737616003073 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 801475232006147 400737616003073 1 2 prime21p hfactor ?_ ?_ ?_
  · rw [show (801475232006147 : ℕ) - 1 = 801475232006146 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((801475232006147 : ℕ) - 1) / 2 = 400737616003073 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((801475232006147 : ℕ) - 1) / 400737616003073 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime22p : Nat.Prime 801354167615489 := by
  have hfactor : (801354167615489 : ℕ) - 1 = 95528861 * 2 ^ 23 := by
    norm_num
  refine prime_from_two_factors 801354167615489 95528861 23 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (801354167615489 : ℕ) - 1 = 801354167615488 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((801354167615489 : ℕ) - 1) / 2 = 400677083807744 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((801354167615489 : ℕ) - 1) / 95528861 = 8388608 by norm_num]
    reduce_mod_char <;> decide

private theorem prime22q : Nat.Prime 1602708335230979 := by
  have hfactor : (1602708335230979 : ℕ) - 1 = 801354167615489 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 1602708335230979 801354167615489 1 2 prime22p hfactor ?_ ?_ ?_
  · rw [show (1602708335230979 : ℕ) - 1 = 1602708335230978 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1602708335230979 : ℕ) - 1) / 2 = 801354167615489 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1602708335230979 : ℕ) - 1) / 801354167615489 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime23p : Nat.Prime 1602691658678273 := by
  have hfactor : (1602691658678273 : ℕ) - 1 = 95527867 * 2 ^ 24 := by
    norm_num
  refine prime_from_two_factors 1602691658678273 95527867 24 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (1602691658678273 : ℕ) - 1 = 1602691658678272 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1602691658678273 : ℕ) - 1) / 2 = 801345829339136 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1602691658678273 : ℕ) - 1) / 95527867 = 16777216 by norm_num]
    reduce_mod_char <;> decide

private theorem prime23q : Nat.Prime 3205383317356547 := by
  have hfactor : (3205383317356547 : ℕ) - 1 = 1602691658678273 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 3205383317356547 1602691658678273 1 2 prime23p hfactor ?_ ?_ ?_
  · rw [show (3205383317356547 : ℕ) - 1 = 3205383317356546 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((3205383317356547 : ℕ) - 1) / 2 = 1602691658678273 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((3205383317356547 : ℕ) - 1) / 1602691658678273 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime24p : Nat.Prime 3205369962692609 := by
  have hfactor : (3205369962692609 : ℕ) - 1 = 95527469 * 2 ^ 25 := by
    norm_num
  refine prime_from_two_factors 3205369962692609 95527469 25 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (3205369962692609 : ℕ) - 1 = 3205369962692608 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((3205369962692609 : ℕ) - 1) / 2 = 1602684981346304 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((3205369962692609 : ℕ) - 1) / 95527469 = 33554432 by norm_num]
    reduce_mod_char <;> decide

private theorem prime24q : Nat.Prime 6410739925385219 := by
  have hfactor : (6410739925385219 : ℕ) - 1 = 3205369962692609 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 6410739925385219 3205369962692609 1 2 prime24p hfactor ?_ ?_ ?_
  · rw [show (6410739925385219 : ℕ) - 1 = 6410739925385218 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((6410739925385219 : ℕ) - 1) / 2 = 3205369962692609 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((6410739925385219 : ℕ) - 1) / 3205369962692609 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime25p : Nat.Prime 1602646259531777 := by
  have hfactor : (1602646259531777 : ℕ) - 1 = 95525161 * 2 ^ 24 := by
    norm_num
  refine prime_from_two_factors 1602646259531777 95525161 24 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (1602646259531777 : ℕ) - 1 = 1602646259531776 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1602646259531777 : ℕ) - 1) / 2 = 801323129765888 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1602646259531777 : ℕ) - 1) / 95525161 = 16777216 by norm_num]
    reduce_mod_char <;> decide

private theorem prime25q : Nat.Prime 12821170076254217 := by
  have hfactor : (12821170076254217 : ℕ) - 1 = 1602646259531777 * 2 ^ 3 := by
    norm_num
  refine prime_from_two_factors 12821170076254217 1602646259531777 3 3 prime25p hfactor ?_ ?_ ?_
  · rw [show (12821170076254217 : ℕ) - 1 = 12821170076254216 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((12821170076254217 : ℕ) - 1) / 2 = 6410585038127108 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((12821170076254217 : ℕ) - 1) / 1602646259531777 = 8 by norm_num]
    reduce_mod_char <;> decide

private theorem prime26p : Nat.Prime 12821077197586433 := by
  have hfactor : (12821077197586433 : ℕ) - 1 = 95524469 * 2 ^ 27 := by
    norm_num
  refine prime_from_two_factors 12821077197586433 95524469 27 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (12821077197586433 : ℕ) - 1 = 12821077197586432 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((12821077197586433 : ℕ) - 1) / 2 = 6410538598793216 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((12821077197586433 : ℕ) - 1) / 95524469 = 134217728 by norm_num]
    reduce_mod_char <;> decide

private theorem prime26q : Nat.Prime 25642154395172867 := by
  have hfactor : (25642154395172867 : ℕ) - 1 = 12821077197586433 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 25642154395172867 12821077197586433 1 2 prime26p hfactor ?_ ?_ ?_
  · rw [show (25642154395172867 : ℕ) - 1 = 25642154395172866 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((25642154395172867 : ℕ) - 1) / 2 = 12821077197586433 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((25642154395172867 : ℕ) - 1) / 12821077197586433 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime27p : Nat.Prime 25641254599524353 := by
  have hfactor : (25641254599524353 : ℕ) - 1 = 95521117 * 2 ^ 28 := by
    norm_num
  refine prime_from_two_factors 25641254599524353 95521117 28 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (25641254599524353 : ℕ) - 1 = 25641254599524352 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((25641254599524353 : ℕ) - 1) / 2 = 12820627299762176 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((25641254599524353 : ℕ) - 1) / 95521117 = 268435456 by norm_num]
    reduce_mod_char <;> decide

private theorem prime27q : Nat.Prime 51282509199048707 := by
  have hfactor : (51282509199048707 : ℕ) - 1 = 25641254599524353 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 51282509199048707 25641254599524353 1 2 prime27p hfactor ?_ ?_ ?_
  · rw [show (51282509199048707 : ℕ) - 1 = 51282509199048706 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((51282509199048707 : ℕ) - 1) / 2 = 25641254599524353 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((51282509199048707 : ℕ) - 1) / 25641254599524353 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime28p : Nat.Prime 51274281115451393 := by
  have hfactor : (51274281115451393 : ℕ) - 1 = 95505791 * 2 ^ 29 := by
    norm_num
  refine prime_from_two_factors 51274281115451393 95505791 29 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (51274281115451393 : ℕ) - 1 = 51274281115451392 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((51274281115451393 : ℕ) - 1) / 2 = 25637140557725696 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((51274281115451393 : ℕ) - 1) / 95505791 = 536870912 by norm_num]
    reduce_mod_char <;> decide

private theorem prime28q : Nat.Prime 102548562230902787 := by
  have hfactor : (102548562230902787 : ℕ) - 1 = 51274281115451393 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 102548562230902787 51274281115451393 1 2 prime28p hfactor ?_ ?_ ?_
  · rw [show (102548562230902787 : ℕ) - 1 = 102548562230902786 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((102548562230902787 : ℕ) - 1) / 2 = 51274281115451393 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((102548562230902787 : ℕ) - 1) / 51274281115451393 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime29p : Nat.Prime 25637108882341889 := by
  have hfactor : (25637108882341889 : ℕ) - 1 = 95505673 * 2 ^ 28 := by
    norm_num
  refine prime_from_two_factors 25637108882341889 95505673 28 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (25637108882341889 : ℕ) - 1 = 25637108882341888 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((25637108882341889 : ℕ) - 1) / 2 = 12818554441170944 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((25637108882341889 : ℕ) - 1) / 95505673 = 268435456 by norm_num]
    reduce_mod_char <;> decide

private theorem prime29q : Nat.Prime 205096871058735113 := by
  have hfactor : (205096871058735113 : ℕ) - 1 = 25637108882341889 * 2 ^ 3 := by
    norm_num
  refine prime_from_two_factors 205096871058735113 25637108882341889 3 3 prime29p hfactor ?_ ?_ ?_
  · rw [show (205096871058735113 : ℕ) - 1 = 205096871058735112 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((205096871058735113 : ℕ) - 1) / 2 = 102548435529367556 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((205096871058735113 : ℕ) - 1) / 25637108882341889 = 8 by norm_num]
    reduce_mod_char <;> decide

private theorem prime30p : Nat.Prime 51274174815010817 := by
  have hfactor : (51274174815010817 : ℕ) - 1 = 95505593 * 2 ^ 29 := by
    norm_num
  refine prime_from_two_factors 51274174815010817 95505593 29 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (51274174815010817 : ℕ) - 1 = 51274174815010816 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((51274174815010817 : ℕ) - 1) / 2 = 25637087407505408 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((51274174815010817 : ℕ) - 1) / 95505593 = 536870912 by norm_num]
    reduce_mod_char <;> decide

private theorem prime30q : Nat.Prime 410193398520086537 := by
  have hfactor : (410193398520086537 : ℕ) - 1 = 51274174815010817 * 2 ^ 3 := by
    norm_num
  refine prime_from_two_factors 410193398520086537 51274174815010817 3 3 prime30p hfactor ?_ ?_ ?_
  · rw [show (410193398520086537 : ℕ) - 1 = 410193398520086536 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((410193398520086537 : ℕ) - 1) / 2 = 205096699260043268 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((410193398520086537 : ℕ) - 1) / 51274174815010817 = 8 by norm_num]
    reduce_mod_char <;> decide

private theorem prime31p : Nat.Prime 102546142016831489 := by
  have hfactor : (102546142016831489 : ℕ) - 1 = 95503537 * 2 ^ 30 := by
    norm_num
  refine prime_from_two_factors 102546142016831489 95503537 30 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (102546142016831489 : ℕ) - 1 = 102546142016831488 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((102546142016831489 : ℕ) - 1) / 2 = 51273071008415744 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((102546142016831489 : ℕ) - 1) / 95503537 = 1073741824 by norm_num]
    reduce_mod_char <;> decide

private theorem prime31q : Nat.Prime 820369136134651913 := by
  have hfactor : (820369136134651913 : ℕ) - 1 = 102546142016831489 * 2 ^ 3 := by
    norm_num
  refine prime_from_two_factors 820369136134651913 102546142016831489 3 3 prime31p hfactor ?_ ?_ ?_
  · rw [show (820369136134651913 : ℕ) - 1 = 820369136134651912 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((820369136134651913 : ℕ) - 1) / 2 = 410184568067325956 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((820369136134651913 : ℕ) - 1) / 102546142016831489 = 8 by norm_num]
    reduce_mod_char <;> decide

private theorem prime32p : Nat.Prime 820289026404646913 := by
  have hfactor : (820289026404646913 : ℕ) - 1 = 95494211 * 2 ^ 33 := by
    norm_num
  refine prime_from_two_factors 820289026404646913 95494211 33 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (820289026404646913 : ℕ) - 1 = 820289026404646912 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((820289026404646913 : ℕ) - 1) / 2 = 410144513202323456 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((820289026404646913 : ℕ) - 1) / 95494211 = 8589934592 by norm_num]
    reduce_mod_char <;> decide

private theorem prime32q : Nat.Prime 1640578052809293827 := by
  have hfactor : (1640578052809293827 : ℕ) - 1 = 820289026404646913 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 1640578052809293827 820289026404646913 1 2 prime32p hfactor ?_ ?_ ?_
  · rw [show (1640578052809293827 : ℕ) - 1 = 1640578052809293826 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1640578052809293827 : ℕ) - 1) / 2 = 820289026404646913 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1640578052809293827 : ℕ) - 1) / 820289026404646913 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime33p : Nat.Prime 1640393987690856449 := by
  have hfactor : (1640393987690856449 : ℕ) - 1 = 95483497 * 2 ^ 34 := by
    norm_num
  refine prime_from_two_factors 1640393987690856449 95483497 34 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (1640393987690856449 : ℕ) - 1 = 1640393987690856448 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1640393987690856449 : ℕ) - 1) / 2 = 820196993845428224 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1640393987690856449 : ℕ) - 1) / 95483497 = 17179869184 by norm_num]
    reduce_mod_char <;> decide

private theorem prime33q : Nat.Prime 3280787975381712899 := by
  have hfactor : (3280787975381712899 : ℕ) - 1 = 1640393987690856449 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 3280787975381712899 1640393987690856449 1 2 prime33p hfactor ?_ ?_ ?_
  · rw [show (3280787975381712899 : ℕ) - 1 = 3280787975381712898 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((3280787975381712899 : ℕ) - 1) / 2 = 1640393987690856449 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((3280787975381712899 : ℕ) - 1) / 1640393987690856449 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime34p : Nat.Prime 3280362395662286849 := by
  have hfactor : (3280362395662286849 : ℕ) - 1 = 95471111 * 2 ^ 35 := by
    norm_num
  refine prime_from_two_factors 3280362395662286849 95471111 35 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (3280362395662286849 : ℕ) - 1 = 3280362395662286848 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((3280362395662286849 : ℕ) - 1) / 2 = 1640181197831143424 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((3280362395662286849 : ℕ) - 1) / 95471111 = 34359738368 by norm_num]
    reduce_mod_char <;> decide

private theorem prime34q : Nat.Prime 6560724791324573699 := by
  have hfactor : (6560724791324573699 : ℕ) - 1 = 3280362395662286849 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 6560724791324573699 3280362395662286849 1 2 prime34p hfactor ?_ ?_ ?_
  · rw [show (6560724791324573699 : ℕ) - 1 = 6560724791324573698 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((6560724791324573699 : ℕ) - 1) / 2 = 3280362395662286849 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((6560724791324573699 : ℕ) - 1) / 3280362395662286849 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime35p : Nat.Prime 1640103510462693377 := by
  have hfactor : (1640103510462693377 : ℕ) - 1 = 95466589 * 2 ^ 34 := by
    norm_num
  refine prime_from_two_factors 1640103510462693377 95466589 34 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (1640103510462693377 : ℕ) - 1 = 1640103510462693376 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1640103510462693377 : ℕ) - 1) / 2 = 820051755231346688 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1640103510462693377 : ℕ) - 1) / 95466589 = 17179869184 by norm_num]
    reduce_mod_char <;> decide

private theorem prime35q : Nat.Prime 13120828083701547017 := by
  have hfactor : (13120828083701547017 : ℕ) - 1 = 1640103510462693377 * 2 ^ 3 := by
    norm_num
  refine prime_from_two_factors 13120828083701547017 1640103510462693377 3 3 prime35p hfactor ?_ ?_ ?_
  · rw [show (13120828083701547017 : ℕ) - 1 = 13120828083701547016 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((13120828083701547017 : ℕ) - 1) / 2 = 6560414041850773508 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((13120828083701547017 : ℕ) - 1) / 1640103510462693377 = 8 by norm_num]
    reduce_mod_char <;> decide

private theorem prime36p : Nat.Prime 13119763206690045953 := by
  have hfactor : (13119763206690045953 : ℕ) - 1 = 95458841 * 2 ^ 37 := by
    norm_num
  refine prime_from_two_factors 13119763206690045953 95458841 37 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (13119763206690045953 : ℕ) - 1 = 13119763206690045952 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((13119763206690045953 : ℕ) - 1) / 2 = 6559881603345022976 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((13119763206690045953 : ℕ) - 1) / 95458841 = 137438953472 by norm_num]
    reduce_mod_char <;> decide

private theorem prime36q : Nat.Prime 26239526413380091907 := by
  have hfactor : (26239526413380091907 : ℕ) - 1 = 13119763206690045953 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 26239526413380091907 13119763206690045953 1 2 prime36p hfactor ?_ ?_ ?_
  · rw [show (26239526413380091907 : ℕ) - 1 = 26239526413380091906 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((26239526413380091907 : ℕ) - 1) / 2 = 13119763206690045953 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((26239526413380091907 : ℕ) - 1) / 13119763206690045953 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime37p : Nat.Prime 6559503646222974977 := by
  have hfactor : (6559503646222974977 : ℕ) - 1 = 95453341 * 2 ^ 36 := by
    norm_num
  refine prime_from_two_factors 6559503646222974977 95453341 36 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (6559503646222974977 : ℕ) - 1 = 6559503646222974976 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((6559503646222974977 : ℕ) - 1) / 2 = 3279751823111487488 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((6559503646222974977 : ℕ) - 1) / 95453341 = 68719476736 by norm_num]
    reduce_mod_char <;> decide

private theorem prime37q : Nat.Prime 52476029169783799817 := by
  have hfactor : (52476029169783799817 : ℕ) - 1 = 6559503646222974977 * 2 ^ 3 := by
    norm_num
  refine prime_from_two_factors 52476029169783799817 6559503646222974977 3 3 prime37p hfactor ?_ ?_ ?_
  · rw [show (52476029169783799817 : ℕ) - 1 = 52476029169783799816 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((52476029169783799817 : ℕ) - 1) / 2 = 26238014584891899908 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((52476029169783799817 : ℕ) - 1) / 6559503646222974977 = 8 by norm_num]
    reduce_mod_char <;> decide

private theorem prime38p : Nat.Prime 13118490796858802177 := by
  have hfactor : (13118490796858802177 : ℕ) - 1 = 95449583 * 2 ^ 37 := by
    norm_num
  refine prime_from_two_factors 13118490796858802177 95449583 37 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (13118490796858802177 : ℕ) - 1 = 13118490796858802176 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((13118490796858802177 : ℕ) - 1) / 2 = 6559245398429401088 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((13118490796858802177 : ℕ) - 1) / 95449583 = 137438953472 by norm_num]
    reduce_mod_char <;> decide

private theorem prime38q : Nat.Prime 104947926374870417417 := by
  have hfactor : (104947926374870417417 : ℕ) - 1 = 13118490796858802177 * 2 ^ 3 := by
    norm_num
  refine prime_from_two_factors 104947926374870417417 13118490796858802177 3 3 prime38p hfactor ?_ ?_ ?_
  · rw [show (104947926374870417417 : ℕ) - 1 = 104947926374870417416 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((104947926374870417417 : ℕ) - 1) / 2 = 52473963187435208708 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((104947926374870417417 : ℕ) - 1) / 13118490796858802177 = 8 by norm_num]
    reduce_mod_char <;> decide

private theorem prime39p : Nat.Prime 26236980494205976577 := by
  have hfactor : (26236980494205976577 : ℕ) - 1 = 95449579 * 2 ^ 38 := by
    norm_num
  refine prime_from_two_factors 26236980494205976577 95449579 38 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (26236980494205976577 : ℕ) - 1 = 26236980494205976576 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((26236980494205976577 : ℕ) - 1) / 2 = 13118490247102988288 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((26236980494205976577 : ℕ) - 1) / 95449579 = 274877906944 by norm_num]
    reduce_mod_char <;> decide

private theorem prime39q : Nat.Prime 209895843953647812617 := by
  have hfactor : (209895843953647812617 : ℕ) - 1 = 26236980494205976577 * 2 ^ 3 := by
    norm_num
  refine prime_from_two_factors 209895843953647812617 26236980494205976577 3 3 prime39p hfactor ?_ ?_ ?_
  · rw [show (209895843953647812617 : ℕ) - 1 = 209895843953647812616 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((209895843953647812617 : ℕ) - 1) / 2 = 104947921976823906308 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((209895843953647812617 : ℕ) - 1) / 26236980494205976577 = 8 by norm_num]
    reduce_mod_char <;> decide

private theorem prime40p : Nat.Prime 52473860932853825537 := by
  have hfactor : (52473860932853825537 : ℕ) - 1 = 95449397 * 2 ^ 39 := by
    norm_num
  refine prime_from_two_factors 52473860932853825537 95449397 39 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (52473860932853825537 : ℕ) - 1 = 52473860932853825536 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((52473860932853825537 : ℕ) - 1) / 2 = 26236930466426912768 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((52473860932853825537 : ℕ) - 1) / 95449397 = 549755813888 by norm_num]
    reduce_mod_char <;> decide

private theorem prime40q : Nat.Prime 419790887462830604297 := by
  have hfactor : (419790887462830604297 : ℕ) - 1 = 52473860932853825537 * 2 ^ 3 := by
    norm_num
  refine prime_from_two_factors 419790887462830604297 52473860932853825537 3 3 prime40p hfactor ?_ ?_ ?_
  · rw [show (419790887462830604297 : ℕ) - 1 = 419790887462830604296 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((419790887462830604297 : ℕ) - 1) / 2 = 209895443731415302148 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((419790887462830604297 : ℕ) - 1) / 52473860932853825537 = 8 by norm_num]
    reduce_mod_char <;> decide

private theorem prime41p : Nat.Prime 104936192386778791937 := by
  have hfactor : (104936192386778791937 : ℕ) - 1 = 95438911 * 2 ^ 40 := by
    norm_num
  refine prime_from_two_factors 104936192386778791937 95438911 40 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (104936192386778791937 : ℕ) - 1 = 104936192386778791936 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((104936192386778791937 : ℕ) - 1) / 2 = 52468096193389395968 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((104936192386778791937 : ℕ) - 1) / 95438911 = 1099511627776 by norm_num]
    reduce_mod_char <;> decide

private theorem prime41q : Nat.Prime 839489539094230335497 := by
  have hfactor : (839489539094230335497 : ℕ) - 1 = 104936192386778791937 * 2 ^ 3 := by
    norm_num
  refine prime_from_two_factors 839489539094230335497 104936192386778791937 3 3 prime41p hfactor ?_ ?_ ?_
  · rw [show (839489539094230335497 : ℕ) - 1 = 839489539094230335496 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((839489539094230335497 : ℕ) - 1) / 2 = 419744769547115167748 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((839489539094230335497 : ℕ) - 1) / 104936192386778791937 = 8 by norm_num]
    reduce_mod_char <;> decide

private theorem prime42p : Nat.Prime 839390565455544451073 := by
  have hfactor : (839390565455544451073 : ℕ) - 1 = 95427659 * 2 ^ 43 := by
    norm_num
  refine prime_from_two_factors 839390565455544451073 95427659 43 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (839390565455544451073 : ℕ) - 1 = 839390565455544451072 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((839390565455544451073 : ℕ) - 1) / 2 = 419695282727772225536 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((839390565455544451073 : ℕ) - 1) / 95427659 = 8796093022208 by norm_num]
    reduce_mod_char <;> decide

private theorem prime42q : Nat.Prime 1678781130911088902147 := by
  have hfactor : (1678781130911088902147 : ℕ) - 1 = 839390565455544451073 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 1678781130911088902147 839390565455544451073 1 2 prime42p hfactor ?_ ?_ ?_
  · rw [show (1678781130911088902147 : ℕ) - 1 = 1678781130911088902146 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1678781130911088902147 : ℕ) - 1) / 2 = 839390565455544451073 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1678781130911088902147 : ℕ) - 1) / 839390565455544451073 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime43p : Nat.Prime 1678662102180312383489 := by
  have hfactor : (1678662102180312383489 : ℕ) - 1 = 95420893 * 2 ^ 44 := by
    norm_num
  refine prime_from_two_factors 1678662102180312383489 95420893 44 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (1678662102180312383489 : ℕ) - 1 = 1678662102180312383488 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1678662102180312383489 : ℕ) - 1) / 2 = 839331051090156191744 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1678662102180312383489 : ℕ) - 1) / 95420893 = 17592186044416 by norm_num]
    reduce_mod_char <;> decide

private theorem prime43q : Nat.Prime 3357324204360624766979 := by
  have hfactor : (3357324204360624766979 : ℕ) - 1 = 1678662102180312383489 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 3357324204360624766979 1678662102180312383489 1 2 prime43p hfactor ?_ ?_ ?_
  · rw [show (3357324204360624766979 : ℕ) - 1 = 3357324204360624766978 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((3357324204360624766979 : ℕ) - 1) / 2 = 1678662102180312383489 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((3357324204360624766979 : ℕ) - 1) / 1678662102180312383489 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime44p : Nat.Prime 839272187635651575809 := by
  have hfactor : (839272187635651575809 : ℕ) - 1 = 95414201 * 2 ^ 43 := by
    norm_num
  refine prime_from_two_factors 839272187635651575809 95414201 43 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (839272187635651575809 : ℕ) - 1 = 839272187635651575808 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((839272187635651575809 : ℕ) - 1) / 2 = 419636093817825787904 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((839272187635651575809 : ℕ) - 1) / 95414201 = 8796093022208 by norm_num]
    reduce_mod_char <;> decide

private theorem prime44q : Nat.Prime 6714177501085212606473 := by
  have hfactor : (6714177501085212606473 : ℕ) - 1 = 839272187635651575809 * 2 ^ 3 := by
    norm_num
  refine prime_from_two_factors 6714177501085212606473 839272187635651575809 3 3 prime44p hfactor ?_ ?_ ?_
  · rw [show (6714177501085212606473 : ℕ) - 1 = 6714177501085212606472 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((6714177501085212606473 : ℕ) - 1) / 2 = 3357088750542606303236 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((6714177501085212606473 : ℕ) - 1) / 839272187635651575809 = 8 by norm_num]
    reduce_mod_char <;> decide

private theorem prime45p : Nat.Prime 6713115355260594946049 := by
  have hfactor : (6713115355260594946049 : ℕ) - 1 = 95399107 * 2 ^ 46 := by
    norm_num
  refine prime_from_two_factors 6713115355260594946049 95399107 46 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (6713115355260594946049 : ℕ) - 1 = 6713115355260594946048 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((6713115355260594946049 : ℕ) - 1) / 2 = 3356557677630297473024 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((6713115355260594946049 : ℕ) - 1) / 95399107 = 70368744177664 by norm_num]
    reduce_mod_char <;> decide

private theorem prime45q : Nat.Prime 13426230710521189892099 := by
  have hfactor : (13426230710521189892099 : ℕ) - 1 = 6713115355260594946049 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 13426230710521189892099 6713115355260594946049 1 2 prime45p hfactor ?_ ?_ ?_
  · rw [show (13426230710521189892099 : ℕ) - 1 = 13426230710521189892098 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((13426230710521189892099 : ℕ) - 1) / 2 = 6713115355260594946049 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((13426230710521189892099 : ℕ) - 1) / 6713115355260594946049 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime46p : Nat.Prime 3356481186805376352257 := by
  have hfactor : (3356481186805376352257 : ℕ) - 1 = 95396933 * 2 ^ 45 := by
    norm_num
  refine prime_from_two_factors 3356481186805376352257 95396933 45 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (3356481186805376352257 : ℕ) - 1 = 3356481186805376352256 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((3356481186805376352257 : ℕ) - 1) / 2 = 1678240593402688176128 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((3356481186805376352257 : ℕ) - 1) / 95396933 = 35184372088832 by norm_num]
    reduce_mod_char <;> decide

private theorem prime46q : Nat.Prime 26851849494443010818057 := by
  have hfactor : (26851849494443010818057 : ℕ) - 1 = 3356481186805376352257 * 2 ^ 3 := by
    norm_num
  refine prime_from_two_factors 26851849494443010818057 3356481186805376352257 3 3 prime46p hfactor ?_ ?_ ?_
  · rw [show (26851849494443010818057 : ℕ) - 1 = 26851849494443010818056 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((26851849494443010818057 : ℕ) - 1) / 2 = 13425924747221505409028 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((26851849494443010818057 : ℕ) - 1) / 3356481186805376352257 = 8 by norm_num]
    reduce_mod_char <;> decide

private theorem prime47p : Nat.Prime 6712514546922806050817 := by
  have hfactor : (6712514546922806050817 : ℕ) - 1 = 95390569 * 2 ^ 46 := by
    norm_num
  refine prime_from_two_factors 6712514546922806050817 95390569 46 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (6712514546922806050817 : ℕ) - 1 = 6712514546922806050816 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((6712514546922806050817 : ℕ) - 1) / 2 = 3356257273461403025408 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((6712514546922806050817 : ℕ) - 1) / 95390569 = 70368744177664 by norm_num]
    reduce_mod_char <;> decide

private theorem prime47q : Nat.Prime 53700116375382448406537 := by
  have hfactor : (53700116375382448406537 : ℕ) - 1 = 6712514546922806050817 * 2 ^ 3 := by
    norm_num
  refine prime_from_two_factors 53700116375382448406537 6712514546922806050817 3 3 prime47p hfactor ?_ ?_ ?_
  · rw [show (53700116375382448406537 : ℕ) - 1 = 53700116375382448406536 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((53700116375382448406537 : ℕ) - 1) / 2 = 26850058187691224203268 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((53700116375382448406537 : ℕ) - 1) / 6712514546922806050817 = 8 by norm_num]
    reduce_mod_char <;> decide

private theorem prime48p : Nat.Prime 13424087278573538246657 := by
  have hfactor : (13424087278573538246657 : ℕ) - 1 = 95383877 * 2 ^ 47 := by
    norm_num
  refine prime_from_two_factors 13424087278573538246657 95383877 47 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (13424087278573538246657 : ℕ) - 1 = 13424087278573538246656 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((13424087278573538246657 : ℕ) - 1) / 2 = 6712043639286769123328 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((13424087278573538246657 : ℕ) - 1) / 95383877 = 140737488355328 by norm_num]
    reduce_mod_char <;> decide

private theorem prime48q : Nat.Prime 107392698228588305973257 := by
  have hfactor : (107392698228588305973257 : ℕ) - 1 = 13424087278573538246657 * 2 ^ 3 := by
    norm_num
  refine prime_from_two_factors 107392698228588305973257 13424087278573538246657 3 3 prime48p hfactor ?_ ?_ ?_
  · rw [show (107392698228588305973257 : ℕ) - 1 = 107392698228588305973256 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((107392698228588305973257 : ℕ) - 1) / 2 = 53696349114294152986628 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((107392698228588305973257 : ℕ) - 1) / 13424087278573538246657 = 8 by norm_num]
    reduce_mod_char <;> decide

private theorem prime49p : Nat.Prime 26847443848107535630337 := by
  have hfactor : (26847443848107535630337 : ℕ) - 1 = 95381281 * 2 ^ 48 := by
    norm_num
  refine prime_from_two_factors 26847443848107535630337 95381281 48 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (26847443848107535630337 : ℕ) - 1 = 26847443848107535630336 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((26847443848107535630337 : ℕ) - 1) / 2 = 13423721924053767815168 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((26847443848107535630337 : ℕ) - 1) / 95381281 = 281474976710656 by norm_num]
    reduce_mod_char <;> decide

private theorem prime49q : Nat.Prime 214779550784860285042697 := by
  have hfactor : (214779550784860285042697 : ℕ) - 1 = 26847443848107535630337 * 2 ^ 3 := by
    norm_num
  refine prime_from_two_factors 214779550784860285042697 26847443848107535630337 3 3 prime49p hfactor ?_ ?_ ?_
  · rw [show (214779550784860285042697 : ℕ) - 1 = 214779550784860285042696 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((214779550784860285042697 : ℕ) - 1) / 2 = 107389775392430142521348 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((214779550784860285042697 : ℕ) - 1) / 26847443848107535630337 = 8 by norm_num]
    reduce_mod_char <;> decide

private theorem prime50p : Nat.Prime 214747052809949179543553 := by
  have hfactor : (214747052809949179543553 : ℕ) - 1 = 95366849 * 2 ^ 51 := by
    norm_num
  refine prime_from_two_factors 214747052809949179543553 95366849 51 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (214747052809949179543553 : ℕ) - 1 = 214747052809949179543552 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((214747052809949179543553 : ℕ) - 1) / 2 = 107373526404974589771776 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((214747052809949179543553 : ℕ) - 1) / 95366849 = 2251799813685248 by norm_num]
    reduce_mod_char <;> decide

private theorem prime50q : Nat.Prime 429494105619898359087107 := by
  have hfactor : (429494105619898359087107 : ℕ) - 1 = 214747052809949179543553 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 429494105619898359087107 214747052809949179543553 1 2 prime50p hfactor ?_ ?_ ?_
  · rw [show (429494105619898359087107 : ℕ) - 1 = 429494105619898359087106 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((429494105619898359087107 : ℕ) - 1) / 2 = 214747052809949179543553 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((429494105619898359087107 : ℕ) - 1) / 214747052809949179543553 = 2 by norm_num]
    reduce_mod_char <;> decide

theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 382613444 ≤ f (k - 1)) (hhi : f (k - 1) ≤ 858988211239796718174213) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  by_cases within0 : f (k - 1) ≤ 765221013
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 382610506 191305253 382610507 4 1
      prime0p prime0q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within0
  by_cases within1 : f (k - 1) ≤ 1530436917
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 765218458 382609229 765218459 4 1
      prime1p prime1q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within1
  by_cases within2 : f (k - 1) ≤ 3060819237
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 1530409618 765204809 1530409619 4 1
      prime2p prime2q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within2
  by_cases within3 : f (k - 1) ≤ 6120811077
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 3060405538 1530202769 3060405539 4 1
      prime3p prime3q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within3
  by_cases within4 : f (k - 1) ≤ 12241353093
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 6120676546 3060338273 6120676547 4 1
      prime4p prime4q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within4
  by_cases within5 : f (k - 1) ≤ 24481921797
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 12240960898 6120480449 12240960899 4 1
      prime5p prime5q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within5
  by_cases within6 : f (k - 1) ≤ 48962871813
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 24481435906 12240717953 24481435907 4 1
      prime6p prime6q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within6
  by_cases within7 : f (k - 1) ≤ 97911036933
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 48955518466 24477759233 48955518467 4 1
      prime7p prime7q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within7
  by_cases within8 : f (k - 1) ≤ 195817756677
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 97908878338 48954439169 97908878339 4 1
      prime8p prime8q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within8
  by_cases within9 : f (k - 1) ≤ 391621783557
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 195810891778 97905445889 195810891779 4 1
      prime9p prime9q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within9
  by_cases within10 : f (k - 1) ≤ 783243108357
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 391621554178 195810777089 391621554179 4 1
      prime10p prime10q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within10
  by_cases within11 : f (k - 1) ≤ 1566485168133
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 783242584066 391621292033 783242584067 4 1
      prime11p prime11q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within11
  by_cases within12 : f (k - 1) ≤ 3132920332293
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 1566460166146 783230083073 1566460166147 4 1
      prime12p prime12q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within12
  by_cases within13 : f (k - 1) ≤ 6265801474053
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 3132900737026 1566450368513 3132900737027 4 1
      prime13p prime13q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within13
  by_cases within14 : f (k - 1) ≤ 12531475283973
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 6265737641986 3132868820993 6265737641987 4 1
      prime14p prime14q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within14
  by_cases within15 : f (k - 1) ≤ 25062166233093
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 12531083116546 6265541558273 12531083116547 4 1
      prime15p prime15q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within15
  by_cases within16 : f (k - 1) ≤ 50121670131717
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 25060835065858 12530417532929 25060835065859 4 1
      prime16p prime16q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within16
  by_cases within17 : f (k - 1) ≤ 100236428050437
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 50118214025218 25059107012609 50118214025219 4 1
      prime17p prime17q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within17
  by_cases within18 : f (k - 1) ≤ 200438676717573
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 100219338358786 50109669179393 100219338358787 4 1
      prime18p prime18q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within18
  by_cases within19 : f (k - 1) ≤ 400814598258693
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 200407299129346 100203649564673 200407299129347 4 1
      prime19p prime19q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within19
  by_cases within20 : f (k - 1) ≤ 801604315906053
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 400802157953026 200401078976513 400802157953027 4 1
      prime20p prime20q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within20
  by_cases within21 : f (k - 1) ≤ 1602950464012293
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 801475232006146 400737616003073 801475232006147 4 1
      prime21p prime21q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within21
  by_cases within22 : f (k - 1) ≤ 3205416670461957
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 1602708335230978 801354167615489 1602708335230979 4 1
      prime22p prime22q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within22
  by_cases within23 : f (k - 1) ≤ 6410766634713093
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 3205383317356546 1602691658678273 3205383317356547 4 1
      prime23p prime23q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within23
  by_cases within24 : f (k - 1) ≤ 12821479850770437
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 6410739925385218 3205369962692609 6410739925385219 4 1
      prime24p prime24q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within24
  by_cases within25 : f (k - 1) ≤ 25642340152508433
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 12821170076254216 1602646259531777 12821170076254217 16 1
      prime25p prime25q ⟨8, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within25
  by_cases within26 : f (k - 1) ≤ 51284308790345733
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 25642154395172866 12821077197586433 25642154395172867 4 1
      prime26p prime26q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within26
  by_cases within27 : f (k - 1) ≤ 102565018398097413
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 51282509199048706 25641254599524353 51282509199048707 4 1
      prime27p prime27q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within27
  by_cases within28 : f (k - 1) ≤ 205097124461805573
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 102548562230902786 51274281115451393 102548562230902787 4 1
      prime28p prime28q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within28
  by_cases within29 : f (k - 1) ≤ 410193742117470225
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 205096871058735112 25637108882341889 205096871058735113 16 1
      prime29p prime29q ⟨8, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within29
  by_cases within30 : f (k - 1) ≤ 820386797040173073
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 410193398520086536 51274174815010817 410193398520086537 16 1
      prime30p prime30q ⟨8, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within30
  by_cases within31 : f (k - 1) ≤ 1640738272269303825
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 820369136134651912 102546142016831489 820369136134651913 16 1
      prime31p prime31q ⟨8, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within31
  by_cases within32 : f (k - 1) ≤ 3281156105618587653
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 1640578052809293826 820289026404646913 1640578052809293827 4 1
      prime32p prime32q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within32
  by_cases within33 : f (k - 1) ≤ 6561575950763425797
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 3280787975381712898 1640393987690856449 3280787975381712899 4 1
      prime33p prime33q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within33
  by_cases within34 : f (k - 1) ≤ 13121449582649147397
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 6560724791324573698 3280362395662286849 6560724791324573699 4 1
      prime34p prime34q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within34
  by_cases within35 : f (k - 1) ≤ 26241656167403094033
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 13120828083701547016 1640103510462693377 13120828083701547017 16 1
      prime35p prime35q ⟨8, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within35
  by_cases within36 : f (k - 1) ≤ 52479052826760183813
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 26239526413380091906 13119763206690045953 26239526413380091907 4 1
      prime36p prime36q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within36
  by_cases within37 : f (k - 1) ≤ 104952058339567599633
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 52476029169783799816 6559503646222974977 52476029169783799817 16 1
      prime37p prime37q ⟨8, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within37
  by_cases within38 : f (k - 1) ≤ 209895852749740834833
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 104947926374870417416 13118490796858802177 104947926374870417417 16 1
      prime38p prime38q ⟨8, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within38
  by_cases within39 : f (k - 1) ≤ 419791687907295625233
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 209895843953647812616 26236980494205976577 209895843953647812617 16 1
      prime39p prime39q ⟨8, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within39
  by_cases within40 : f (k - 1) ≤ 839581774925661208593
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 419790887462830604296 52473860932853825537 419790887462830604297 16 1
      prime40p prime40q ⟨8, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within40
  by_cases within41 : f (k - 1) ≤ 1678979078188460670993
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 839489539094230335496 104936192386778791937 839489539094230335497 16 1
      prime41p prime41q ⟨8, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within41
  by_cases within42 : f (k - 1) ≤ 3357562261822177804293
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 1678781130911088902146 839390565455544451073 1678781130911088902147 4 1
      prime42p prime42q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within42
  by_cases within43 : f (k - 1) ≤ 6714648408721249533957
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 3357324204360624766978 1678662102180312383489 3357324204360624766979 4 1
      prime43p prime43q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within43
  by_cases within44 : f (k - 1) ≤ 13428355002170425212945
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 6714177501085212606472 839272187635651575809 6714177501085212606473 16 1
      prime44p prime44q ⟨8, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within44
  by_cases within45 : f (k - 1) ≤ 26852461421042379784197
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 13426230710521189892098 6713115355260594946049 13426230710521189892099 4 1
      prime45p prime45q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within45
  by_cases within46 : f (k - 1) ≤ 53703698988886021636113
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 26851849494443010818056 3356481186805376352257 26851849494443010818057 16 1
      prime46p prime46q ⟨8, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within46
  by_cases within47 : f (k - 1) ≤ 107400232750764896813073
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 53700116375382448406536 6712514546922806050817 53700116375382448406537 16 1
      prime47p prime47q ⟨8, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within47
  by_cases within48 : f (k - 1) ≤ 214785396457176611946513
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 107392698228588305973256 13424087278573538246657 107392698228588305973257 16 1
      prime48p prime48q ⟨8, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within48
  by_cases within49 : f (k - 1) ≤ 429559101569720570085393
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 214779550784860285042696 26847443848107535630337 214779550784860285042697 16 1
      prime49p prime49q ⟨8, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within49
  by_cases within50 : f (k - 1) ≤ 858988211239796718174213
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 429494105619898359087106 214747052809949179543553 429494105619898359087107 4 1
      prime50p prime50q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within50
  omega

