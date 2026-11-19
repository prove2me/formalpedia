-- Prove2me | solution 1 for ECDLP.n_prime
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T07:28:00.134333+00:00
-- url     : https://prove2.me/submissions/efd22f13-c56f-4db1-aca4-12e406816469

import Mathlib
import Definitions.Def_ECDLPChallengeData

lemma lucas_cert (p : ℕ) (a : ZMod p) (PL : List (ℕ × ℕ))
    (hprime : ∀ x ∈ PL, x.1.Prime) (hprod : p - 1 = (PL.map fun x => x.1 ^ x.2).prod)
    (ha : a ^ (p - 1) = 1) (hd : ∀ x ∈ PL, a ^ ((p - 1) / x.1) ≠ 1) : p.Prime := by
  apply lucas_primality p a ha
  intro q hq hqd
  rw [hprod] at hqd
  obtain ⟨y, hy, hqy⟩ := (Prime.dvd_prod_iff hq.prime).mp hqd
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  have hqx : q ∣ x.1 := hq.dvd_of_dvd_pow hqy
  have heq : q = x.1 := (Nat.prime_dvd_prime_iff_eq hq (hprime x hx)).mp hqx
  rw [heq]
  exact hd x hx
theorem prime_1874947822879 : Nat.Prime 1874947822879 :=
  lucas_cert 1874947822879 (3 : ZMod 1874947822879) [(2, 1), (3, 1), (13, 1), (19, 1), (13399, 1), (94421, 1)]
    (by simp only [List.forall_mem_cons]; exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩)
    (by norm_num)
    (by reduce_mod_char)
    (by simp only [List.forall_mem_cons]; exact ⟨by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by simp⟩)

theorem prime_51107327756035783 : Nat.Prime 51107327756035783 :=
  lucas_cert 51107327756035783 (5 : ZMod 51107327756035783) [(2, 1), (3, 1), (7, 1), (11, 1), (59, 1), (1874947822879, 1)]
    (by simp only [List.forall_mem_cons]; exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_1874947822879, by simp⟩)
    (by norm_num)
    (by reduce_mod_char)
    (by simp only [List.forall_mem_cons]; exact ⟨by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by simp⟩)

theorem prime_2217595152162583667 : Nat.Prime 2217595152162583667 :=
  lucas_cert 2217595152162583667 (2 : ZMod 2217595152162583667) [(2, 1), (11, 1), (4003, 1), (24659, 1), (28687, 1), (35597, 1)]
    (by simp only [List.forall_mem_cons]; exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩)
    (by norm_num)
    (by reduce_mod_char)
    (by simp only [List.forall_mem_cons]; exact ⟨by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by simp⟩)

theorem prime_66527854564877510011 : Nat.Prime 66527854564877510011 :=
  lucas_cert 66527854564877510011 (2 : ZMod 66527854564877510011) [(2, 1), (3, 1), (5, 1), (2217595152162583667, 1)]
    (by simp only [List.forall_mem_cons]; exact ⟨by norm_num, by norm_num, by norm_num, prime_2217595152162583667, by simp⟩)
    (by norm_num)
    (by reduce_mod_char)
    (by simp only [List.forall_mem_cons]; exact ⟨by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by simp⟩)

theorem prime_14090612407 : Nat.Prime 14090612407 :=
  lucas_cert 14090612407 (5 : ZMod 14090612407) [(2, 1), (3, 1), (13, 1), (23, 1), (61, 1), (331, 1), (389, 1)]
    (by simp only [List.forall_mem_cons]; exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩)
    (by norm_num)
    (by reduce_mod_char)
    (by simp only [List.forall_mem_cons]; exact ⟨by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by simp⟩)

theorem prime_8031641 : Nat.Prime 8031641 :=
  lucas_cert 8031641 (3 : ZMod 8031641) [(2, 3), (5, 1), (199, 1), (1009, 1)]
    (by simp only [List.forall_mem_cons]; exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩)
    (by norm_num)
    (by reduce_mod_char)
    (by simp only [List.forall_mem_cons]; exact ⟨by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by simp⟩)

theorem prime_48189847 : Nat.Prime 48189847 :=
  lucas_cert 48189847 (47 : ZMod 48189847) [(2, 1), (3, 1), (8031641, 1)]
    (by simp only [List.forall_mem_cons]; exact ⟨by norm_num, by norm_num, prime_8031641, by simp⟩)
    (by norm_num)
    (by reduce_mod_char)
    (by simp only [List.forall_mem_cons]; exact ⟨by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by simp⟩)

theorem prime_942356930322483209823491 : Nat.Prime 942356930322483209823491 :=
  lucas_cert 942356930322483209823491 (2 : ZMod 942356930322483209823491) [(2, 1), (5, 1), (137, 1), (1013, 1), (48189847, 1), (14090612407, 1)]
    (by simp only [List.forall_mem_cons]; exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_48189847, prime_14090612407, by simp⟩)
    (by norm_num)
    (by reduce_mod_char)
    (by simp only [List.forall_mem_cons]; exact ⟨by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by simp⟩)

theorem prime_58426129679993959009056443 : Nat.Prime 58426129679993959009056443 :=
  lucas_cert 58426129679993959009056443 (2 : ZMod 58426129679993959009056443) [(2, 1), (31, 1), (942356930322483209823491, 1)]
    (by simp only [List.forall_mem_cons]; exact ⟨by norm_num, by norm_num, prime_942356930322483209823491, by simp⟩)
    (by norm_num)
    (by reduce_mod_char)
    (by simp only [List.forall_mem_cons]; exact ⟨by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by simp⟩)

theorem prime_64467157784386614394756842980429 : Nat.Prime 64467157784386614394756842980429 :=
  lucas_cert 64467157784386614394756842980429 (2 : ZMod 64467157784386614394756842980429) [(2, 2), (7, 1), (157, 1), (251, 1), (58426129679993959009056443, 1)]
    (by simp only [List.forall_mem_cons]; exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_58426129679993959009056443, by simp⟩)
    (by norm_num)
    (by reduce_mod_char)
    (by simp only [List.forall_mem_cons]; exact ⟨by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by simp⟩)

theorem prime_18406372847737621097080107628624365276513063062857122317960690589425712086189 : Nat.Prime 18406372847737621097080107628624365276513063062857122317960690589425712086189 :=
  lucas_cert 18406372847737621097080107628624365276513063062857122317960690589425712086189 (3 : ZMod 18406372847737621097080107628624365276513063062857122317960690589425712086189) [(2, 2), (23, 1), (613, 1), (1489, 1), (51107327756035783, 1), (66527854564877510011, 1), (64467157784386614394756842980429, 1)]
    (by simp only [List.forall_mem_cons]; exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_51107327756035783, prime_66527854564877510011, prime_64467157784386614394756842980429, by simp⟩)
    (by norm_num)
    (by reduce_mod_char)
    (by simp only [List.forall_mem_cons]; exact ⟨by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by simp⟩)


theorem solution : Nat.Prime ECDLP.n := prime_18406372847737621097080107628624365276513063062857122317960690589425712086189
