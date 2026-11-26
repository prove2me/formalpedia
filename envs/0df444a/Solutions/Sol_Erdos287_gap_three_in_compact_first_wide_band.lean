-- Prove2me | solution 1 for Erdos287.gap_three_in_compact_first_wide_band
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T10:50:02.398915+00:00
-- url     : https://prove2.me/submissions/35eb9637-e7ae-451b-a15a-59a0fb634e80

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

private theorem prime0p : Nat.Prime 429452555409736238891009 := by
  have hfactor : (429452555409736238891009 : ℕ) - 1 = 95357623 * 2 ^ 52 := by
    norm_num
  refine prime_from_two_factors 429452555409736238891009 95357623 52 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (429452555409736238891009 : ℕ) - 1 = 429452555409736238891008 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((429452555409736238891009 : ℕ) - 1) / 2 = 214726277704868119445504 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((429452555409736238891009 : ℕ) - 1) / 95357623 = 4503599627370496 by norm_num]
    reduce_mod_char <;> decide

private theorem prime0q : Nat.Prime 858905110819472477782019 := by
  have hfactor : (858905110819472477782019 : ℕ) - 1 = 429452555409736238891009 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 858905110819472477782019 429452555409736238891009 1 2 prime0p hfactor ?_ ?_ ?_
  · rw [show (858905110819472477782019 : ℕ) - 1 = 858905110819472477782018 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((858905110819472477782019 : ℕ) - 1) / 2 = 429452555409736238891009 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((858905110819472477782019 : ℕ) - 1) / 429452555409736238891009 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime1p : Nat.Prime 1073045472464619509383169 := by
  have hfactor : (1073045472464619509383169 : ℕ) - 1 = 119131979 * 2 ^ 53 := by
    norm_num
  refine prime_from_two_factors 1073045472464619509383169 119131979 53 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (1073045472464619509383169 : ℕ) - 1 = 1073045472464619509383168 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1073045472464619509383169 : ℕ) - 1) / 2 = 536522736232309754691584 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1073045472464619509383169 : ℕ) - 1) / 119131979 = 9007199254740992 by norm_num]
    reduce_mod_char <;> decide

private theorem prime1q : Nat.Prime 2146090944929239018766339 := by
  have hfactor : (2146090944929239018766339 : ℕ) - 1 = 1073045472464619509383169 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 2146090944929239018766339 1073045472464619509383169 1 2 prime1p hfactor ?_ ?_ ?_
  · rw [show (2146090944929239018766339 : ℕ) - 1 = 2146090944929239018766338 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((2146090944929239018766339 : ℕ) - 1) / 2 = 1073045472464619509383169 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((2146090944929239018766339 : ℕ) - 1) / 1073045472464619509383169 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime2p : Nat.Prime 2681537289325409833320449 := by
  have hfactor : (2681537289325409833320449 : ℕ) - 1 = 74427611 * 2 ^ 55 := by
    norm_num
  refine prime_from_two_factors 2681537289325409833320449 74427611 55 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (2681537289325409833320449 : ℕ) - 1 = 2681537289325409833320448 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((2681537289325409833320449 : ℕ) - 1) / 2 = 1340768644662704916660224 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((2681537289325409833320449 : ℕ) - 1) / 74427611 = 36028797018963968 by norm_num]
    reduce_mod_char <;> decide

private theorem prime2q : Nat.Prime 5363074578650819666640899 := by
  have hfactor : (5363074578650819666640899 : ℕ) - 1 = 2681537289325409833320449 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 5363074578650819666640899 2681537289325409833320449 1 2 prime2p hfactor ?_ ?_ ?_
  · rw [show (5363074578650819666640899 : ℕ) - 1 = 5363074578650819666640898 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((5363074578650819666640899 : ℕ) - 1) / 2 = 2681537289325409833320449 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((5363074578650819666640899 : ℕ) - 1) / 2681537289325409833320449 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime3p : Nat.Prime 6703499454546768138600449 := by
  have hfactor : (6703499454546768138600449 : ℕ) - 1 = 93029743 * 2 ^ 56 := by
    norm_num
  refine prime_from_two_factors 6703499454546768138600449 93029743 56 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (6703499454546768138600449 : ℕ) - 1 = 6703499454546768138600448 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((6703499454546768138600449 : ℕ) - 1) / 2 = 3351749727273384069300224 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((6703499454546768138600449 : ℕ) - 1) / 93029743 = 72057594037927936 by norm_num]
    reduce_mod_char <;> decide

private theorem prime3q : Nat.Prime 13406998909093536277200899 := by
  have hfactor : (13406998909093536277200899 : ℕ) - 1 = 6703499454546768138600449 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 13406998909093536277200899 6703499454546768138600449 1 2 prime3p hfactor ?_ ?_ ?_
  · rw [show (13406998909093536277200899 : ℕ) - 1 = 13406998909093536277200898 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((13406998909093536277200899 : ℕ) - 1) / 2 = 6703499454546768138600449 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((13406998909093536277200899 : ℕ) - 1) / 6703499454546768138600449 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime4p : Nat.Prime 16756749794737105244520449 := by
  have hfactor : (16756749794737105244520449 : ℕ) - 1 = 116273309 * 2 ^ 57 := by
    norm_num
  refine prime_from_two_factors 16756749794737105244520449 116273309 57 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (16756749794737105244520449 : ℕ) - 1 = 16756749794737105244520448 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((16756749794737105244520449 : ℕ) - 1) / 2 = 8378374897368552622260224 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((16756749794737105244520449 : ℕ) - 1) / 116273309 = 144115188075855872 by norm_num]
    reduce_mod_char <;> decide

private theorem prime4q : Nat.Prime 33513499589474210489040899 := by
  have hfactor : (33513499589474210489040899 : ℕ) - 1 = 16756749794737105244520449 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 33513499589474210489040899 16756749794737105244520449 1 2 prime4p hfactor ?_ ?_ ?_
  · rw [show (33513499589474210489040899 : ℕ) - 1 = 33513499589474210489040898 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((33513499589474210489040899 : ℕ) - 1) / 2 = 16756749794737105244520449 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((33513499589474210489040899 : ℕ) - 1) / 16756749794737105244520449 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime5p : Nat.Prime 41876011944264035769253889 := by
  have hfactor : (41876011944264035769253889 : ℕ) - 1 = 72643301 * 2 ^ 59 := by
    norm_num
  refine prime_from_two_factors 41876011944264035769253889 72643301 59 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (41876011944264035769253889 : ℕ) - 1 = 41876011944264035769253888 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((41876011944264035769253889 : ℕ) - 1) / 2 = 20938005972132017884626944 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((41876011944264035769253889 : ℕ) - 1) / 72643301 = 576460752303423488 by norm_num]
    reduce_mod_char <;> decide

private theorem prime5q : Nat.Prime 83752023888528071538507779 := by
  have hfactor : (83752023888528071538507779 : ℕ) - 1 = 41876011944264035769253889 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 83752023888528071538507779 41876011944264035769253889 1 2 prime5p hfactor ?_ ?_ ?_
  · rw [show (83752023888528071538507779 : ℕ) - 1 = 83752023888528071538507778 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((83752023888528071538507779 : ℕ) - 1) / 2 = 41876011944264035769253889 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((83752023888528071538507779 : ℕ) - 1) / 41876011944264035769253889 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime6p : Nat.Prime 104659185463416966294274049 := by
  have hfactor : (104659185463416966294274049 : ℕ) - 1 = 90777373 * 2 ^ 60 := by
    norm_num
  refine prime_from_two_factors 104659185463416966294274049 90777373 60 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (104659185463416966294274049 : ℕ) - 1 = 104659185463416966294274048 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((104659185463416966294274049 : ℕ) - 1) / 2 = 52329592731708483147137024 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((104659185463416966294274049 : ℕ) - 1) / 90777373 = 1152921504606846976 by norm_num]
    reduce_mod_char <;> decide

private theorem prime6q : Nat.Prime 209318370926833932588548099 := by
  have hfactor : (209318370926833932588548099 : ℕ) - 1 = 104659185463416966294274049 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 209318370926833932588548099 104659185463416966294274049 1 2 prime6p hfactor ?_ ?_ ?_
  · rw [show (209318370926833932588548099 : ℕ) - 1 = 209318370926833932588548098 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((209318370926833932588548099 : ℕ) - 1) / 2 = 104659185463416966294274049 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((209318370926833932588548099 : ℕ) - 1) / 104659185463416966294274049 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime7p : Nat.Prime 65409514871589272654184449 := by
  have hfactor : (65409514871589272654184449 : ℕ) - 1 = 113467421 * 2 ^ 59 := by
    norm_num
  refine prime_from_two_factors 65409514871589272654184449 113467421 59 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (65409514871589272654184449 : ℕ) - 1 = 65409514871589272654184448 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((65409514871589272654184449 : ℕ) - 1) / 2 = 32704757435794636327092224 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((65409514871589272654184449 : ℕ) - 1) / 113467421 = 576460752303423488 by norm_num]
    reduce_mod_char <;> decide

private theorem prime7q : Nat.Prime 523276118972714181233475593 := by
  have hfactor : (523276118972714181233475593 : ℕ) - 1 = 65409514871589272654184449 * 2 ^ 3 := by
    norm_num
  refine prime_from_two_factors 523276118972714181233475593 65409514871589272654184449 3 3 prime7p hfactor ?_ ?_ ?_
  · rw [show (523276118972714181233475593 : ℕ) - 1 = 523276118972714181233475592 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((523276118972714181233475593 : ℕ) - 1) / 2 = 261638059486357090616737796 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((523276118972714181233475593 : ℕ) - 1) / 65409514871589272654184449 = 8 by norm_num]
    reduce_mod_char <;> decide

private theorem prime8p : Nat.Prime 163498494098774740474789889 := by
  have hfactor : (163498494098774740474789889 : ℕ) - 1 = 70906169 * 2 ^ 61 := by
    norm_num
  refine prime_from_two_factors 163498494098774740474789889 70906169 61 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (163498494098774740474789889 : ℕ) - 1 = 163498494098774740474789888 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((163498494098774740474789889 : ℕ) - 1) / 2 = 81749247049387370237394944 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((163498494098774740474789889 : ℕ) - 1) / 70906169 = 2305843009213693952 by norm_num]
    reduce_mod_char <;> decide

private theorem prime8q : Nat.Prime 1307987952790197923798319113 := by
  have hfactor : (1307987952790197923798319113 : ℕ) - 1 = 163498494098774740474789889 * 2 ^ 3 := by
    norm_num
  refine prime_from_two_factors 1307987952790197923798319113 163498494098774740474789889 3 3 prime8p hfactor ?_ ?_ ?_
  · rw [show (1307987952790197923798319113 : ℕ) - 1 = 1307987952790197923798319112 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1307987952790197923798319113 : ℕ) - 1) / 2 = 653993976395098961899159556 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1307987952790197923798319113 : ℕ) - 1) / 163498494098774740474789889 = 8 by norm_num]
    reduce_mod_char <;> decide

private theorem prime9p : Nat.Prime 1634949260373022832047685633 := by
  have hfactor : (1634949260373022832047685633 : ℕ) - 1 = 88630777 * 2 ^ 64 := by
    norm_num
  refine prime_from_two_factors 1634949260373022832047685633 88630777 64 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (1634949260373022832047685633 : ℕ) - 1 = 1634949260373022832047685632 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1634949260373022832047685633 : ℕ) - 1) / 2 = 817474630186511416023842816 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1634949260373022832047685633 : ℕ) - 1) / 88630777 = 18446744073709551616 by norm_num]
    reduce_mod_char <;> decide

private theorem prime9q : Nat.Prime 3269898520746045664095371267 := by
  have hfactor : (3269898520746045664095371267 : ℕ) - 1 = 1634949260373022832047685633 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 3269898520746045664095371267 1634949260373022832047685633 1 2 prime9p hfactor ?_ ?_ ?_
  · rw [show (3269898520746045664095371267 : ℕ) - 1 = 3269898520746045664095371266 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((3269898520746045664095371267 : ℕ) - 1) / 2 = 1634949260373022832047685633 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((3269898520746045664095371267 : ℕ) - 1) / 1634949260373022832047685633 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime10p : Nat.Prime 4087289393491090401900101633 := by
  have hfactor : (4087289393491090401900101633 : ℕ) - 1 = 110786201 * 2 ^ 65 := by
    norm_num
  refine prime_from_two_factors 4087289393491090401900101633 110786201 65 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (4087289393491090401900101633 : ℕ) - 1 = 4087289393491090401900101632 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((4087289393491090401900101633 : ℕ) - 1) / 2 = 2043644696745545200950050816 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((4087289393491090401900101633 : ℕ) - 1) / 110786201 = 36893488147419103232 by norm_num]
    reduce_mod_char <;> decide

private theorem prime10q : Nat.Prime 8174578786982180803800203267 := by
  have hfactor : (8174578786982180803800203267 : ℕ) - 1 = 4087289393491090401900101633 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 8174578786982180803800203267 4087289393491090401900101633 1 2 prime10p hfactor ?_ ?_ ?_
  · rw [show (8174578786982180803800203267 : ℕ) - 1 = 8174578786982180803800203266 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((8174578786982180803800203267 : ℕ) - 1) / 2 = 4087289393491090401900101633 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((8174578786982180803800203267 : ℕ) - 1) / 4087289393491090401900101633 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime11p : Nat.Prime 2554501762019877292645285889 := by
  have hfactor : (2554501762019877292645285889 : ℕ) - 1 = 69239909 * 2 ^ 65 := by
    norm_num
  refine prime_from_two_factors 2554501762019877292645285889 69239909 65 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (2554501762019877292645285889 : ℕ) - 1 = 2554501762019877292645285888 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((2554501762019877292645285889 : ℕ) - 1) / 2 = 1277250881009938646322642944 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((2554501762019877292645285889 : ℕ) - 1) / 69239909 = 36893488147419103232 by norm_num]
    reduce_mod_char <;> decide

private theorem prime11q : Nat.Prime 20436014096159018341162287113 := by
  have hfactor : (20436014096159018341162287113 : ℕ) - 1 = 2554501762019877292645285889 * 2 ^ 3 := by
    norm_num
  refine prime_from_two_factors 20436014096159018341162287113 2554501762019877292645285889 3 3 prime11p hfactor ?_ ?_ ?_
  · rw [show (20436014096159018341162287113 : ℕ) - 1 = 20436014096159018341162287112 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((20436014096159018341162287113 : ℕ) - 1) / 2 = 10218007048079509170581143556 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((20436014096159018341162287113 : ℕ) - 1) / 2554501762019877292645285889 = 8 by norm_num]
    reduce_mod_char <;> decide

private theorem prime12p : Nat.Prime 6383996578915303403624071169 := by
  have hfactor : (6383996578915303403624071169 : ℕ) - 1 = 86519287 * 2 ^ 66 := by
    norm_num
  refine prime_from_two_factors 6383996578915303403624071169 86519287 66 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (6383996578915303403624071169 : ℕ) - 1 = 6383996578915303403624071168 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((6383996578915303403624071169 : ℕ) - 1) / 2 = 3191998289457651701812035584 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((6383996578915303403624071169 : ℕ) - 1) / 86519287 = 73786976294838206464 by norm_num]
    reduce_mod_char <;> decide

private theorem prime12q : Nat.Prime 51071972631322427228992569353 := by
  have hfactor : (51071972631322427228992569353 : ℕ) - 1 = 6383996578915303403624071169 * 2 ^ 3 := by
    norm_num
  refine prime_from_two_factors 51071972631322427228992569353 6383996578915303403624071169 3 3 prime12p hfactor ?_ ?_ ?_
  · rw [show (51071972631322427228992569353 : ℕ) - 1 = 51071972631322427228992569352 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((51071972631322427228992569353 : ℕ) - 1) / 2 = 25535986315661213614496284676 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((51071972631322427228992569353 : ℕ) - 1) / 6383996578915303403624071169 = 8 by norm_num]
    reduce_mod_char <;> decide

private theorem prime13p : Nat.Prime 15958810597413124065823031297 := by
  have hfactor : (15958810597413124065823031297 : ℕ) - 1 = 108141107 * 2 ^ 67 := by
    norm_num
  refine prime_from_two_factors 15958810597413124065823031297 108141107 67 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (15958810597413124065823031297 : ℕ) - 1 = 15958810597413124065823031296 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((15958810597413124065823031297 : ℕ) - 1) / 2 = 7979405298706562032911515648 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((15958810597413124065823031297 : ℕ) - 1) / 108141107 = 147573952589676412928 by norm_num]
    reduce_mod_char <;> decide

private theorem prime13q : Nat.Prime 127670484779304992526584250377 := by
  have hfactor : (127670484779304992526584250377 : ℕ) - 1 = 15958810597413124065823031297 * 2 ^ 3 := by
    norm_num
  refine prime_from_two_factors 127670484779304992526584250377 15958810597413124065823031297 3 3 prime13p hfactor ?_ ?_ ?_
  · rw [show (127670484779304992526584250377 : ℕ) - 1 = 127670484779304992526584250376 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((127670484779304992526584250377 : ℕ) - 1) / 2 = 63835242389652496263292125188 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((127670484779304992526584250377 : ℕ) - 1) / 15958810597413124065823031297 = 8 by norm_num]
    reduce_mod_char <;> decide

private theorem prime14p : Nat.Prime 39893751015868106001734434817 := by
  have hfactor : (39893751015868106001734434817 : ℕ) - 1 = 67582643 * 2 ^ 69 := by
    norm_num
  refine prime_from_two_factors 39893751015868106001734434817 67582643 69 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (39893751015868106001734434817 : ℕ) - 1 = 39893751015868106001734434816 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((39893751015868106001734434817 : ℕ) - 1) / 2 = 19946875507934053000867217408 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((39893751015868106001734434817 : ℕ) - 1) / 67582643 = 590295810358705651712 by norm_num]
    reduce_mod_char <;> decide

private theorem prime14q : Nat.Prime 319150008126944848013875478537 := by
  have hfactor : (319150008126944848013875478537 : ℕ) - 1 = 39893751015868106001734434817 * 2 ^ 3 := by
    norm_num
  refine prime_from_two_factors 319150008126944848013875478537 39893751015868106001734434817 3 3 prime14p hfactor ?_ ?_ ?_
  · rw [show (319150008126944848013875478537 : ℕ) - 1 = 319150008126944848013875478536 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((319150008126944848013875478537 : ℕ) - 1) / 2 = 159575004063472424006937739268 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((319150008126944848013875478537 : ℕ) - 1) / 39893751015868106001734434817 = 8 by norm_num]
    reduce_mod_char <;> decide

private theorem prime15p : Nat.Prime 398820599712256276928200179713 := by
  have hfactor : (398820599712256276928200179713 : ℕ) - 1 = 84453547 * 2 ^ 72 := by
    norm_num
  refine prime_from_two_factors 398820599712256276928200179713 84453547 72 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (398820599712256276928200179713 : ℕ) - 1 = 398820599712256276928200179712 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((398820599712256276928200179713 : ℕ) - 1) / 2 = 199410299856128138464100089856 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((398820599712256276928200179713 : ℕ) - 1) / 84453547 = 4722366482869645213696 by norm_num]
    reduce_mod_char <;> decide

private theorem prime15q : Nat.Prime 797641199424512553856400359427 := by
  have hfactor : (797641199424512553856400359427 : ℕ) - 1 = 398820599712256276928200179713 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 797641199424512553856400359427 398820599712256276928200179713 1 2 prime15p hfactor ?_ ?_ ?_
  · rw [show (797641199424512553856400359427 : ℕ) - 1 = 797641199424512553856400359426 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((797641199424512553856400359427 : ℕ) - 1) / 2 = 398820599712256276928200179713 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((797641199424512553856400359427 : ℕ) - 1) / 398820599712256276928200179713 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime16p : Nat.Prime 249243166613939726974531403777 := by
  have hfactor : (249243166613939726974531403777 : ℕ) - 1 = 105558587 * 2 ^ 71 := by
    norm_num
  refine prime_from_two_factors 249243166613939726974531403777 105558587 71 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (249243166613939726974531403777 : ℕ) - 1 = 249243166613939726974531403776 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((249243166613939726974531403777 : ℕ) - 1) / 2 = 124621583306969863487265701888 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((249243166613939726974531403777 : ℕ) - 1) / 105558587 = 2361183241434822606848 by norm_num]
    reduce_mod_char <;> decide

private theorem prime16q : Nat.Prime 1993945332911517815796251230217 := by
  have hfactor : (1993945332911517815796251230217 : ℕ) - 1 = 249243166613939726974531403777 * 2 ^ 3 := by
    norm_num
  refine prime_from_two_factors 1993945332911517815796251230217 249243166613939726974531403777 3 3 prime16p hfactor ?_ ?_ ?_
  · rw [show (1993945332911517815796251230217 : ℕ) - 1 = 1993945332911517815796251230216 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1993945332911517815796251230217 : ℕ) - 1) / 2 = 996972666455758907898125615108 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1993945332911517815796251230217 : ℕ) - 1) / 249243166613939726974531403777 = 8 by norm_num]
    reduce_mod_char <;> decide

private theorem prime17p : Nat.Prime 2492274113826429289772049498113 := by
  have hfactor : (2492274113826429289772049498113 : ℕ) - 1 = 131939893 * 2 ^ 74 := by
    norm_num
  refine prime_from_two_factors 2492274113826429289772049498113 131939893 74 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (2492274113826429289772049498113 : ℕ) - 1 = 2492274113826429289772049498112 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((2492274113826429289772049498113 : ℕ) - 1) / 2 = 1246137056913214644886024749056 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((2492274113826429289772049498113 : ℕ) - 1) / 131939893 = 18889465931478580854784 by norm_num]
    reduce_mod_char <;> decide

private theorem prime17q : Nat.Prime 4984548227652858579544098996227 := by
  have hfactor : (4984548227652858579544098996227 : ℕ) - 1 = 2492274113826429289772049498113 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 4984548227652858579544098996227 2492274113826429289772049498113 1 2 prime17p hfactor ?_ ?_ ?_
  · rw [show (4984548227652858579544098996227 : ℕ) - 1 = 4984548227652858579544098996226 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((4984548227652858579544098996227 : ℕ) - 1) / 2 = 2492274113826429289772049498113 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((4984548227652858579544098996227 : ℕ) - 1) / 2492274113826429289772049498113 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime18p : Nat.Prime 1557541812601908847522367930369 := by
  have hfactor : (1557541812601908847522367930369 : ℕ) - 1 = 82455577 * 2 ^ 74 := by
    norm_num
  refine prime_from_two_factors 1557541812601908847522367930369 82455577 74 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (1557541812601908847522367930369 : ℕ) - 1 = 1557541812601908847522367930368 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1557541812601908847522367930369 : ℕ) - 1) / 2 = 778770906300954423761183965184 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1557541812601908847522367930369 : ℕ) - 1) / 82455577 = 18889465931478580854784 by norm_num]
    reduce_mod_char <;> decide

private theorem prime18q : Nat.Prime 12460334500815270780178943442953 := by
  have hfactor : (12460334500815270780178943442953 : ℕ) - 1 = 1557541812601908847522367930369 * 2 ^ 3 := by
    norm_num
  refine prime_from_two_factors 12460334500815270780178943442953 1557541812601908847522367930369 3 3 prime18p hfactor ?_ ?_ ?_
  · rw [show (12460334500815270780178943442953 : ℕ) - 1 = 12460334500815270780178943442952 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((12460334500815270780178943442953 : ℕ) - 1) / 2 = 6230167250407635390089471721476 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((12460334500815270780178943442953 : ℕ) - 1) / 1557541812601908847522367930369 = 8 by norm_num]
    reduce_mod_char <;> decide

private theorem prime19p : Nat.Prime 15573423058406337570470958727169 := by
  have hfactor : (15573423058406337570470958727169 : ℕ) - 1 = 103056269 * 2 ^ 77 := by
    norm_num
  refine prime_from_two_factors 15573423058406337570470958727169 103056269 77 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (15573423058406337570470958727169 : ℕ) - 1 = 15573423058406337570470958727168 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((15573423058406337570470958727169 : ℕ) - 1) / 2 = 7786711529203168785235479363584 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((15573423058406337570470958727169 : ℕ) - 1) / 103056269 = 151115727451828646838272 by norm_num]
    reduce_mod_char <;> decide

private theorem prime19q : Nat.Prime 31146846116812675140941917454339 := by
  have hfactor : (31146846116812675140941917454339 : ℕ) - 1 = 15573423058406337570470958727169 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 31146846116812675140941917454339 15573423058406337570470958727169 1 2 prime19p hfactor ?_ ?_ ?_
  · rw [show (31146846116812675140941917454339 : ℕ) - 1 = 31146846116812675140941917454338 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((31146846116812675140941917454339 : ℕ) - 1) / 2 = 15573423058406337570470958727169 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((31146846116812675140941917454339 : ℕ) - 1) / 15573423058406337570470958727169 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime20p : Nat.Prime 9730900138794044802680724914177 := by
  have hfactor : (9730900138794044802680724914177 : ℕ) - 1 = 128787391 * 2 ^ 76 := by
    norm_num
  refine prime_from_two_factors 9730900138794044802680724914177 128787391 76 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (9730900138794044802680724914177 : ℕ) - 1 = 9730900138794044802680724914176 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((9730900138794044802680724914177 : ℕ) - 1) / 2 = 4865450069397022401340362457088 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((9730900138794044802680724914177 : ℕ) - 1) / 128787391 = 75557863725914323419136 by norm_num]
    reduce_mod_char <;> decide

private theorem prime20q : Nat.Prime 77847201110352358421445799313417 := by
  have hfactor : (77847201110352358421445799313417 : ℕ) - 1 = 9730900138794044802680724914177 * 2 ^ 3 := by
    norm_num
  refine prime_from_two_factors 77847201110352358421445799313417 9730900138794044802680724914177 3 3 prime20p hfactor ?_ ?_ ?_
  · rw [show (77847201110352358421445799313417 : ℕ) - 1 = 77847201110352358421445799313416 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((77847201110352358421445799313417 : ℕ) - 1) / 2 = 38923600555176179210722899656708 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((77847201110352358421445799313417 : ℕ) - 1) / 9730900138794044802680724914177 = 8 by norm_num]
    reduce_mod_char <;> decide

private theorem prime21p : Nat.Prime 97289039151459788914388560248833 := by
  have hfactor : (97289039151459788914388560248833 : ℕ) - 1 = 80475607 * 2 ^ 80 := by
    norm_num
  refine prime_from_two_factors 97289039151459788914388560248833 80475607 80 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (97289039151459788914388560248833 : ℕ) - 1 = 97289039151459788914388560248832 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((97289039151459788914388560248833 : ℕ) - 1) / 2 = 48644519575729894457194280124416 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((97289039151459788914388560248833 : ℕ) - 1) / 80475607 = 1208925819614629174706176 by norm_num]
    reduce_mod_char <;> decide

private theorem prime21q : Nat.Prime 194578078302919577828777120497667 := by
  have hfactor : (194578078302919577828777120497667 : ℕ) - 1 = 97289039151459788914388560248833 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 194578078302919577828777120497667 97289039151459788914388560248833 1 2 prime21p hfactor ?_ ?_ ?_
  · rw [show (194578078302919577828777120497667 : ℕ) - 1 = 194578078302919577828777120497666 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((194578078302919577828777120497667 : ℕ) - 1) / 2 = 97289039151459788914388560248833 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((194578078302919577828777120497667 : ℕ) - 1) / 97289039151459788914388560248833 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime22p : Nat.Prime 60781808394689475421367116496897 := by
  have hfactor : (60781808394689475421367116496897 : ℕ) - 1 = 100555067 * 2 ^ 79 := by
    norm_num
  refine prime_from_two_factors 60781808394689475421367116496897 100555067 79 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (60781808394689475421367116496897 : ℕ) - 1 = 60781808394689475421367116496896 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((60781808394689475421367116496897 : ℕ) - 1) / 2 = 30390904197344737710683558248448 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((60781808394689475421367116496897 : ℕ) - 1) / 100555067 = 604462909807314587353088 by norm_num]
    reduce_mod_char <;> decide

private theorem prime22q : Nat.Prime 486254467157515803370936931975177 := by
  have hfactor : (486254467157515803370936931975177 : ℕ) - 1 = 60781808394689475421367116496897 * 2 ^ 3 := by
    norm_num
  refine prime_from_two_factors 486254467157515803370936931975177 60781808394689475421367116496897 3 3 prime22p hfactor ?_ ?_ ?_
  · rw [show (486254467157515803370936931975177 : ℕ) - 1 = 486254467157515803370936931975176 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((486254467157515803370936931975177 : ℕ) - 1) / 2 = 243127233578757901685468465987588 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((486254467157515803370936931975177 : ℕ) - 1) / 60781808394689475421367116496897 = 8 by norm_num]
    reduce_mod_char <;> decide

private theorem prime23p : Nat.Prime 151935972740104796201647568060417 := by
  have hfactor : (151935972740104796201647568060417 : ℕ) - 1 = 125678491 * 2 ^ 80 := by
    norm_num
  refine prime_from_two_factors 151935972740104796201647568060417 125678491 80 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (151935972740104796201647568060417 : ℕ) - 1 = 151935972740104796201647568060416 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((151935972740104796201647568060417 : ℕ) - 1) / 2 = 75967986370052398100823784030208 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((151935972740104796201647568060417 : ℕ) - 1) / 125678491 = 1208925819614629174706176 by norm_num]
    reduce_mod_char <;> decide

private theorem prime23q : Nat.Prime 1215487781920838369613180544483337 := by
  have hfactor : (1215487781920838369613180544483337 : ℕ) - 1 = 151935972740104796201647568060417 * 2 ^ 3 := by
    norm_num
  refine prime_from_two_factors 1215487781920838369613180544483337 151935972740104796201647568060417 3 3 prime23p hfactor ?_ ?_ ?_
  · rw [show (1215487781920838369613180544483337 : ℕ) - 1 = 1215487781920838369613180544483336 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1215487781920838369613180544483337 : ℕ) - 1) / 2 = 607743890960419184806590272241668 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((1215487781920838369613180544483337 : ℕ) - 1) / 151935972740104796201647568060417 = 8 by norm_num]
    reduce_mod_char <;> decide

private theorem prime24p : Nat.Prime 379760771992056534393073747099649 := by
  have hfactor : (379760771992056534393073747099649 : ℕ) - 1 = 78532687 * 2 ^ 82 := by
    norm_num
  refine prime_from_two_factors 379760771992056534393073747099649 78532687 82 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (379760771992056534393073747099649 : ℕ) - 1 = 379760771992056534393073747099648 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((379760771992056534393073747099649 : ℕ) - 1) / 2 = 189880385996028267196536873549824 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((379760771992056534393073747099649 : ℕ) - 1) / 78532687 = 4835703278458516698824704 by norm_num]
    reduce_mod_char <;> decide

private theorem prime24q : Nat.Prime 3038086175936452275144589976797193 := by
  have hfactor : (3038086175936452275144589976797193 : ℕ) - 1 = 379760771992056534393073747099649 * 2 ^ 3 := by
    norm_num
  refine prime_from_two_factors 3038086175936452275144589976797193 379760771992056534393073747099649 3 3 prime24p hfactor ?_ ?_ ?_
  · rw [show (3038086175936452275144589976797193 : ℕ) - 1 = 3038086175936452275144589976797192 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((3038086175936452275144589976797193 : ℕ) - 1) / 2 = 1519043087968226137572294988398596 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((3038086175936452275144589976797193 : ℕ) - 1) / 379760771992056534393073747099649 = 8 by norm_num]
    reduce_mod_char <;> decide

private theorem prime25p : Nat.Prime 949260420377252165179268311023617 := by
  have hfactor : (949260420377252165179268311023617 : ℕ) - 1 = 98151227 * 2 ^ 83 := by
    norm_num
  refine prime_from_two_factors 949260420377252165179268311023617 98151227 83 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (949260420377252165179268311023617 : ℕ) - 1 = 949260420377252165179268311023616 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((949260420377252165179268311023617 : ℕ) - 1) / 2 = 474630210188626082589634155511808 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((949260420377252165179268311023617 : ℕ) - 1) / 98151227 = 9671406556917033397649408 by norm_num]
    reduce_mod_char <;> decide

private theorem prime25q : Nat.Prime 7594083363018017321434146488188937 := by
  have hfactor : (7594083363018017321434146488188937 : ℕ) - 1 = 949260420377252165179268311023617 * 2 ^ 3 := by
    norm_num
  refine prime_from_two_factors 7594083363018017321434146488188937 949260420377252165179268311023617 3 3 prime25p hfactor ?_ ?_ ?_
  · rw [show (7594083363018017321434146488188937 : ℕ) - 1 = 7594083363018017321434146488188936 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((7594083363018017321434146488188937 : ℕ) - 1) / 2 = 3797041681509008660717073244094468 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((7594083363018017321434146488188937 : ℕ) - 1) / 949260420377252165179268311023617 = 8 by norm_num]
    reduce_mod_char <;> decide

private theorem prime26p : Nat.Prime 9490454308123358336770586032734209 := by
  have hfactor : (9490454308123358336770586032734209 : ℕ) - 1 = 122661247 * 2 ^ 86 := by
    norm_num
  refine prime_from_two_factors 9490454308123358336770586032734209 122661247 86 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (9490454308123358336770586032734209 : ℕ) - 1 = 9490454308123358336770586032734208 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((9490454308123358336770586032734209 : ℕ) - 1) / 2 = 4745227154061679168385293016367104 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((9490454308123358336770586032734209 : ℕ) - 1) / 122661247 = 77371252455336267181195264 by norm_num]
    reduce_mod_char <;> decide

private theorem prime26q : Nat.Prime 18980908616246716673541172065468419 := by
  have hfactor : (18980908616246716673541172065468419 : ℕ) - 1 = 9490454308123358336770586032734209 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 18980908616246716673541172065468419 9490454308123358336770586032734209 1 2 prime26p hfactor ?_ ?_ ?_
  · rw [show (18980908616246716673541172065468419 : ℕ) - 1 = 18980908616246716673541172065468418 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((18980908616246716673541172065468419 : ℕ) - 1) / 2 = 9490454308123358336770586032734209 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((18980908616246716673541172065468419 : ℕ) - 1) / 9490454308123358336770586032734209 = 2 by norm_num]
    reduce_mod_char <;> decide

private theorem prime27p : Nat.Prime 5927425500057500933943194608992257 := by
  have hfactor : (5927425500057500933943194608992257 : ℕ) - 1 = 76610179 * 2 ^ 86 := by
    norm_num
  refine prime_from_two_factors 5927425500057500933943194608992257 76610179 86 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (5927425500057500933943194608992257 : ℕ) - 1 = 5927425500057500933943194608992256 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((5927425500057500933943194608992257 : ℕ) - 1) / 2 = 2963712750028750466971597304496128 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((5927425500057500933943194608992257 : ℕ) - 1) / 76610179 = 77371252455336267181195264 by norm_num]
    reduce_mod_char <;> decide

private theorem prime27q : Nat.Prime 47419404000460007471545556871938057 := by
  have hfactor : (47419404000460007471545556871938057 : ℕ) - 1 = 5927425500057500933943194608992257 * 2 ^ 3 := by
    norm_num
  refine prime_from_two_factors 47419404000460007471545556871938057 5927425500057500933943194608992257 3 3 prime27p hfactor ?_ ?_ ?_
  · rw [show (47419404000460007471545556871938057 : ℕ) - 1 = 47419404000460007471545556871938056 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((47419404000460007471545556871938057 : ℕ) - 1) / 2 = 23709702000230003735772778435969028 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((47419404000460007471545556871938057 : ℕ) - 1) / 5927425500057500933943194608992257 = 8 by norm_num]
    reduce_mod_char <;> decide

private theorem prime28p : Nat.Prime 14818185752889881789524672793018369 := by
  have hfactor : (14818185752889881789524672793018369 : ℕ) - 1 = 95760281 * 2 ^ 87 := by
    norm_num
  refine prime_from_two_factors 14818185752889881789524672793018369 95760281 87 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (14818185752889881789524672793018369 : ℕ) - 1 = 14818185752889881789524672793018368 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((14818185752889881789524672793018369 : ℕ) - 1) / 2 = 7409092876444940894762336396509184 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((14818185752889881789524672793018369 : ℕ) - 1) / 95760281 = 154742504910672534362390528 by norm_num]
    reduce_mod_char <;> decide

private theorem prime28q : Nat.Prime 118545486023119054316197382344146953 := by
  have hfactor : (118545486023119054316197382344146953 : ℕ) - 1 = 14818185752889881789524672793018369 * 2 ^ 3 := by
    norm_num
  refine prime_from_two_factors 118545486023119054316197382344146953 14818185752889881789524672793018369 3 3 prime28p hfactor ?_ ?_ ?_
  · rw [show (118545486023119054316197382344146953 : ℕ) - 1 = 118545486023119054316197382344146952 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((118545486023119054316197382344146953 : ℕ) - 1) / 2 = 59272743011559527158098691172073476 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((118545486023119054316197382344146953 : ℕ) - 1) / 14818185752889881789524672793018369 = 8 by norm_num]
    reduce_mod_char <;> decide

private theorem prime29p : Nat.Prime 148114062671102383508527083566399489 := by
  have hfactor : (148114062671102383508527083566399489 : ℕ) - 1 = 119645587 * 2 ^ 90 := by
    norm_num
  refine prime_from_two_factors 148114062671102383508527083566399489 119645587 90 3 (by norm_num) hfactor ?_ ?_ ?_
  · rw [show (148114062671102383508527083566399489 : ℕ) - 1 = 148114062671102383508527083566399488 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((148114062671102383508527083566399489 : ℕ) - 1) / 2 = 74057031335551191754263541783199744 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((148114062671102383508527083566399489 : ℕ) - 1) / 119645587 = 1237940039285380274899124224 by norm_num]
    reduce_mod_char <;> decide

private theorem prime29q : Nat.Prime 296228125342204767017054167132798979 := by
  have hfactor : (296228125342204767017054167132798979 : ℕ) - 1 = 148114062671102383508527083566399489 * 2 ^ 1 := by
    norm_num
  refine prime_from_two_factors 296228125342204767017054167132798979 148114062671102383508527083566399489 1 2 prime29p hfactor ?_ ?_ ?_
  · rw [show (296228125342204767017054167132798979 : ℕ) - 1 = 296228125342204767017054167132798978 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((296228125342204767017054167132798979 : ℕ) - 1) / 2 = 148114062671102383508527083566399489 by norm_num]
    reduce_mod_char <;> decide
  · rw [show ((296228125342204767017054167132798979 : ℕ) - 1) / 148114062671102383508527083566399489 = 2 by norm_num]
    reduce_mod_char <;> decide

theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 858988211239796718174214 ≤ f (k - 1)) (hhi : f (k - 1) ≤ 740570313355511917542635417831997435) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  by_cases within0 : f (k - 1) ≤ 2147262777048681194455035
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 858905110819472477782018 429452555409736238891009 858905110819472477782019 6 2
      prime0p prime0q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within0
  by_cases within1 : f (k - 1) ≤ 5365227362323097546915835
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 2146090944929239018766338 1073045472464619509383169 2146090944929239018766339 6 2
      prime1p prime1q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within1
  by_cases within2 : f (k - 1) ≤ 13407686446627049166602235
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 5363074578650819666640898 2681537289325409833320449 5363074578650819666640899 6 2
      prime2p prime2q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within2
  by_cases within3 : f (k - 1) ≤ 33517497272733840693002235
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 13406998909093536277200898 6703499454546768138600449 13406998909093536277200899 6 2
      prime3p prime3q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within3
  by_cases within4 : f (k - 1) ≤ 83783748973685526222602235
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 33513499589474210489040898 16756749794737105244520449 33513499589474210489040899 6 2
      prime4p prime4q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within4
  by_cases within5 : f (k - 1) ≤ 209380059721320178846269435
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 83752023888528071538507778 41876011944264035769253889 83752023888528071538507779 6 2
      prime5p prime5q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within5
  by_cases within6 : f (k - 1) ≤ 523295927317084831471370235
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 209318370926833932588548098 104659185463416966294274049 209318370926833932588548099 6 2
      prime6p prime6q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within6
  by_cases within7 : f (k - 1) ≤ 1308190297431785453083688970
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 523276118972714181233475592 65409514871589272654184449 523276118972714181233475593 24 2
      prime7p prime7q ⟨8, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within7
  by_cases within8 : f (k - 1) ≤ 3269969881975494809495797770
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 1307987952790197923798319112 163498494098774740474789889 1307987952790197923798319113 24 2
      prime8p prime8q ⟨8, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within8
  by_cases within9 : f (k - 1) ≤ 8174746301865114160238428155
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 3269898520746045664095371266 1634949260373022832047685633 3269898520746045664095371267 6 2
      prime9p prime9q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within9
  by_cases within10 : f (k - 1) ≤ 20436446967455452009500508155
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 8174578786982180803800203266 4087289393491090401900101633 8174578786982180803800203267 6 2
      prime10p prime10q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within10
  by_cases within11 : f (k - 1) ≤ 51090035240397545852905717770
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 20436014096159018341162287112 2554501762019877292645285889 20436014096159018341162287113 24 2
      prime11p prime11q ⟨8, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within11
  by_cases within12 : f (k - 1) ≤ 127679931578306068072481423370
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 51071972631322427228992569352 6383996578915303403624071169 51071972631322427228992569353 24 2
      prime12p prime12q ⟨8, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within12
  by_cases within13 : f (k - 1) ≤ 319176211948262481316460625930
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 127670484779304992526584250376 15958810597413124065823031297 127670484779304992526584250377 24 2
      prime13p prime13q ⟨8, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within13
  by_cases within14 : f (k - 1) ≤ 797875020317362120034688696330
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 319150008126944848013875478536 39893751015868106001734434817 319150008126944848013875478537 24 2
      prime14p prime14q ⟨8, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within14
  by_cases within15 : f (k - 1) ≤ 1994102998561281384641000898555
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 797641199424512553856400359426 398820599712256276928200179713 797641199424512553856400359427 6 2
      prime15p prime15q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within15
  by_cases within16 : f (k - 1) ≤ 4984863332278794539490628075530
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 1993945332911517815796251230216 249243166613939726974531403777 1993945332911517815796251230217 24 2
      prime16p prime16q ⟨8, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within16
  by_cases within17 : f (k - 1) ≤ 12461370569132146448860247490555
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 4984548227652858579544098996226 2492274113826429289772049498113 4984548227652858579544098996227 6 2
      prime17p prime17q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within17
  by_cases within18 : f (k - 1) ≤ 31150836252038176950447358607370
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 12460334500815270780178943442952 1557541812601908847522367930369 12460334500815270780178943442953 24 2
      prime18p prime18q ⟨8, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within18
  by_cases within19 : f (k - 1) ≤ 77867115292031687852354793635835
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 31146846116812675140941917454338 15573423058406337570470958727169 31146846116812675140941917454339 6 2
      prime19p prime19q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within19
  by_cases within20 : f (k - 1) ≤ 194618002775880896053614498283530
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 77847201110352358421445799313416 9730900138794044802680724914177 77847201110352358421445799313417 24 2
      prime20p prime20q ⟨8, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within20
  by_cases within21 : f (k - 1) ≤ 486445195757298944571942801244155
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 194578078302919577828777120497666 97289039151459788914388560248833 194578078302919577828777120497667 6 2
      prime21p prime21q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within21
  by_cases within22 : f (k - 1) ≤ 1215636167893789508427342329937930
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 486254467157515803370936931975176 60781808394689475421367116496897 486254467157515803370936931975177 24 2
      prime22p prime22q ⟨8, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within22
  by_cases within23 : f (k - 1) ≤ 3038719454802095924032951361208330
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 1215487781920838369613180544483336 151935972740104796201647568060417 1215487781920838369613180544483337 24 2
      prime23p prime23q ⟨8, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within23
  by_cases within24 : f (k - 1) ≤ 7595215439841130687861474941992970
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 3038086175936452275144589976797192 379760771992056534393073747099649 3038086175936452275144589976797193 24 2
      prime24p prime24q ⟨8, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within24
  by_cases within25 : f (k - 1) ≤ 18985208407545043303585366220472330
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 7594083363018017321434146488188936 949260420377252165179268311023617 7594083363018017321434146488188937 24 2
      prime25p prime25q ⟨8, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within25
  by_cases within26 : f (k - 1) ≤ 47452271540616791683852930163671035
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 18980908616246716673541172065468418 9490454308123358336770586032734209 18980908616246716673541172065468419 6 2
      prime26p prime26q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within26
  by_cases within27 : f (k - 1) ≤ 118548510001150018678863892179845130
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 47419404000460007471545556871938056 5927425500057500933943194608992257 47419404000460007471545556871938057 24 2
      prime27p prime27q ⟨8, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within27
  by_cases within28 : f (k - 1) ≤ 296363715057797635790493455860367370
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 118545486023119054316197382344146952 14818185752889881789524672793018369 118545486023119054316197382344146953 24 2
      prime28p prime28q ⟨8, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within28
  by_cases within29 : f (k - 1) ≤ 740570313355511917542635417831997435
  · exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum 296228125342204767017054167132798978 148114062671102383508527083566399489 296228125342204767017054167132798979 6 2
      prime29p prime29q ⟨2, by norm_num⟩ ⟨1, by norm_num⟩
      (by norm_num [Nat.factorial]) (by norm_num [Nat.factorial])
      (by omega) (by omega) (by omega) (by omega)
  push_neg at within29
  omega

