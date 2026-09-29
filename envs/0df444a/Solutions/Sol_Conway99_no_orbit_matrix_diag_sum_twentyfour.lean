-- Prove2me | solution 1 for Conway99.no_orbit_matrix_diag_sum_twentyfour
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-07T13:29:30.010737+00:00
-- url     : https://prove2.me/submissions/68c0c769-259c-4205-8a94-2abd88858ae0

import Mathlib

open Finset Matrix



namespace Wil24

variable {C : Matrix (Fin 9) (Fin 9) ℕ}

section Basic
variable (hs : ∀ i j, C i j = C j i) (hr : ∀ i, ∑ j, C i j = 14)
  (hq : ∀ i j, (∑ k, C i k * C k j) + C i j = (if i = j then 12 else 0) + 22)

include hr in
lemma rowZ (i : Fin 9) : ∑ k, ((C i k : ℤ)) = 14 := by
  have h : ((∑ k, C i k : ℕ) : ℤ) = ((14 : ℕ) : ℤ) := by rw [hr i]
  push_cast at h
  exact h

include hs hq in
lemma sqZ (i : Fin 9) : ∑ k, ((C i k : ℤ))^2 = 34 - (C i i : ℤ) := by
  have h := hq i i
  rw [if_pos rfl] at h
  have h2 : ∑ k, C i k * C i k = ∑ k, C i k * C k i := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hs k i]
  have h3 : ((∑ k, C i k * C i k : ℕ) : ℤ) + ((C i i : ℕ) : ℤ) = ((34 : ℕ) : ℤ) := by
    rw [← Nat.cast_add, h2, h]
  push_cast at h3
  have : ∑ k, ((C i k : ℤ))^2 = ∑ k, ((C i k : ℤ)) * ((C i k : ℤ)) := by
    refine Finset.sum_congr rfl (fun k _ => by ring)
  rw [this]
  linarith [h3]

include hs hq in
lemma offZ {i j : Fin 9} (hij : i ≠ j) :
    ∑ k, ((C i k : ℤ)) * ((C j k : ℤ)) = 22 - (C i j : ℤ) := by
  have h := hq i j
  rw [if_neg hij] at h
  have h2 : ∑ k, C i k * C j k = ∑ k, C i k * C k j := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hs k j]
  have h3 : ((∑ k, C i k * C j k : ℕ) : ℤ) + ((C i j : ℕ) : ℤ) = ((0 + 22 : ℕ) : ℤ) := by
    rw [← Nat.cast_add, h2, h]
  push_cast at h3
  linarith [h3]

include hr in
lemma rowErase (i : Fin 9) : ∑ k ∈ univ.erase i, ((C i k : ℤ)) = 14 - (C i i : ℤ) := by
  have := Finset.add_sum_erase univ (fun k => ((C i k : ℤ))) (Finset.mem_univ i)
  rw [rowZ hr i] at this
  linarith [this]

include hs hq in
lemma sqErase (i : Fin 9) :
    ∑ k ∈ univ.erase i, ((C i k : ℤ))^2 = 34 - (C i i : ℤ) - (C i i : ℤ)^2 := by
  have := Finset.add_sum_erase univ (fun k => ((C i k : ℤ))^2) (Finset.mem_univ i)
  rw [sqZ hs hq i] at this
  linarith [this]

include hs hq in
lemma entry_le (i j : Fin 9) : (C i j : ℤ) ≤ 5 := by
  by_contra hc
  push_neg at hc
  have hmem : j ∈ (univ : Finset (Fin 9)) := Finset.mem_univ j
  have hle : ((C i j : ℤ))^2 ≤ ∑ k, ((C i k : ℤ))^2 :=
    Finset.single_le_sum (f := fun k => ((C i k : ℤ))^2) (fun k _ => sq_nonneg _) hmem
  rw [sqZ hs hq i] at hle
  have hdnn : (0 : ℤ) ≤ (C i i : ℤ) := by positivity
  nlinarith [hle, hc, hdnn]

end Basic

section Rows
variable (hs : ∀ i j, C i j = C j i) (hr : ∀ i, ∑ j, C i j = 14)
  (hq : ∀ i j, (∑ k, C i k * C k j) + C i j = (if i = j then 12 else 0) + 22)

include hs hr hq in
/-- A row with diagonal entry `4` has all off-diagonal entries in `{1,2}`,
with exactly two entries equal to `2`. -/
lemma four_row {i : Fin 9} (hi : C i i = 4) :
    (∀ k, k ≠ i → C i k = 1 ∨ C i k = 2) ∧
      (univ.filter (fun k => C i k = 2)).card = 2 := by
  classical
  have hcard : (univ.erase i).card = 8 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp
  have h1 : ∑ k ∈ univ.erase i, ((C i k : ℤ)) = 10 := by
    rw [rowErase hr i, hi]; norm_num
  have h2 : ∑ k ∈ univ.erase i, ((C i k : ℤ))^2 = 14 := by
    rw [sqErase hs hq i, hi]; norm_num
  have h3 : ∑ k ∈ univ.erase i, (((C i k : ℤ)) - 1) * (((C i k : ℤ)) - 2) = 0 := by
    have e : ∀ k, (((C i k : ℤ)) - 1) * (((C i k : ℤ)) - 2)
        = ((C i k : ℤ))^2 - 3 * ((C i k : ℤ)) + 2 := by intro k; ring
    simp only [e]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      hcard, h1, h2]
    norm_num
  have hnn : ∀ k ∈ univ.erase i, 0 ≤ (((C i k : ℤ)) - 1) * (((C i k : ℤ)) - 2) := by
    intro k _
    have hcase : (C i k : ℤ) ≤ 1 ∨ (2 : ℤ) ≤ (C i k : ℤ) := by omega
    rcases hcase with h | h <;> nlinarith
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h3
  have hval : ∀ k, k ≠ i → C i k = 1 ∨ C i k = 2 := by
    intro k hk
    have hk' : k ∈ univ.erase i := Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩
    have := hzero k hk'
    rcases mul_eq_zero.mp this with h | h
    · left; omega
    · right; omega
  refine ⟨hval, ?_⟩
  have hsum1 : ∑ k ∈ univ.erase i, (((C i k : ℤ)) - 1) = 2 := by
    rw [Finset.sum_sub_distrib, h1, Finset.sum_const, hcard]
    norm_num
  have hbool : ∑ k ∈ univ.erase i, (if C i k = 2 then (1 : ℤ) else 0) = 2 := by
    rw [← hsum1]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' : k ≠ i := (Finset.mem_erase.mp hk).1
    rcases hval k hk' with h | h <;> rw [h] <;> norm_num
  have hfil : ((univ.erase i).filter (fun k => C i k = 2)) = univ.filter (fun k => C i k = 2) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rintro rfl
      omega
  rw [Finset.sum_boole] at hbool
  rw [← hfil]
  exact_mod_cast hbool

end Rows

end Wil24

namespace Wil24

variable {C : Matrix (Fin 9) (Fin 9) ℕ}

section Pairs
variable (hs : ∀ i j, C i j = C j i) (hr : ∀ i, ∑ j, C i j = 14)
  (hq : ∀ i j, (∑ k, C i k * C k j) + C i j = (if i = j then 12 else 0) + 22)

lemma sdiff_pair (i j : Fin 9) (hij : i ≠ j) :
    (univ \ ({i, j} : Finset (Fin 9))) = (univ.erase i).erase j := by
  ext k
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_erase, not_or]
  tauto

lemma card_sdiff_pair (i j : Fin 9) (hij : i ≠ j) :
    (univ \ ({i, j} : Finset (Fin 9))).card = 7 := by
  rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_pair hij]
  simp

include hs hr hq in
lemma sum_off_pair {i j : Fin 9} (hi : C i i = 4) (hj : C j j = 4) (hij : i ≠ j) :
    ∑ k ∈ univ \ ({i, j} : Finset (Fin 9)), ((C i k : ℤ)) * ((C j k : ℤ))
      = 22 - 9 * (C i j : ℤ) := by
  have hsub : ({i, j} : Finset (Fin 9)) ⊆ univ := Finset.subset_univ _
  have hsplit := Finset.sum_sdiff (f := fun k => ((C i k : ℤ)) * ((C j k : ℤ))) hsub
  rw [Finset.sum_pair hij, offZ hs hq hij] at hsplit
  have hji : (C j i : ℤ) = (C i j : ℤ) := by rw [hs j i]
  rw [hi, hj, hji] at hsplit
  push_cast at hsplit ⊢
  linarith [hsplit]

include hs hr hq in
lemma pair_one {i j : Fin 9} (hi : C i i = 4) (hj : C j j = 4) (hij : i ≠ j) :
    C i j = 1 := by
  classical
  obtain ⟨hvi, -⟩ := four_row hs hr hq hi
  obtain ⟨hvj, -⟩ := four_row hs hr hq hj
  have hge : ∀ k ∈ univ \ ({i, j} : Finset (Fin 9)),
      (1 : ℤ) ≤ ((C i k : ℤ)) * ((C j k : ℤ)) := by
    intro k hk
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hk
    rcases hvi k hk.1 with h1 | h1 <;> rcases hvj k hk.2 with h2 | h2 <;>
      rw [h1, h2] <;> norm_num
  have hR : (7 : ℤ) ≤ ∑ k ∈ univ \ ({i, j} : Finset (Fin 9)),
      ((C i k : ℤ)) * ((C j k : ℤ)) := by
    calc (7 : ℤ) = ∑ _k ∈ univ \ ({i, j} : Finset (Fin 9)), (1 : ℤ) := by
          rw [Finset.sum_const, card_sdiff_pair i j hij]; norm_num
      _ ≤ _ := Finset.sum_le_sum hge
  rw [sum_off_pair hs hr hq hi hj hij] at hR
  rcases hvi j (Ne.symm hij) with h | h
  · exact h
  · rw [h] at hR; norm_num at hR

include hs hr hq in
lemma pair_supp {i j : Fin 9} (hi : C i i = 4) (hj : C j j = 4) (hij : i ≠ j) :
    univ.filter (fun k => C i k = 2) = univ.filter (fun k => C j k = 2) := by
  classical
  obtain ⟨hvi, -⟩ := four_row hs hr hq hi
  obtain ⟨hvj, -⟩ := four_row hs hr hq hj
  have hij1 : C i j = 1 := pair_one hs hr hq hi hj hij
  have hji1 : C j i = 1 := by rw [hs j i]; exact hij1
  have hR : ∑ k ∈ univ \ ({i, j} : Finset (Fin 9)), ((C i k : ℤ)) * ((C j k : ℤ)) = 13 := by
    rw [sum_off_pair hs hr hq hi hj hij, hij1]; norm_num
  -- the row sums restricted to the complement of {i,j}
  have hrowrest : ∀ (a b : Fin 9), a ≠ b → C a a = 4 → C a b = 1 →
      ∑ k ∈ univ \ ({a, b} : Finset (Fin 9)), ((C a k : ℤ)) = 9 := by
    intro a b hab ha hab1
    have h1 : ∑ k ∈ univ.erase a, ((C a k : ℤ)) = 10 := by
      rw [rowErase hr a, ha]; norm_num
    have hbmem : b ∈ univ.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩
    have := Finset.add_sum_erase (univ.erase a) (fun k => ((C a k : ℤ))) hbmem
    rw [h1, hab1] at this
    rw [sdiff_pair a b hab]
    push_cast at this ⊢
    linarith [this]
  have hA : ∑ k ∈ univ \ ({i, j} : Finset (Fin 9)), ((C i k : ℤ)) = 9 :=
    hrowrest i j hij hi hij1
  have hB : ∑ k ∈ univ \ ({i, j} : Finset (Fin 9)), ((C j k : ℤ)) = 9 := by
    have := hrowrest j i (Ne.symm hij) hj hji1
    rw [show ({j, i} : Finset (Fin 9)) = ({i, j} : Finset (Fin 9)) from
      Finset.pair_comm j i] at this
    exact this
  have hcard7 := card_sdiff_pair i j hij
  -- the two nonnegative sums that vanish
  have hzero1 : ∑ k ∈ univ \ ({i, j} : Finset (Fin 9)),
      ((C i k : ℤ) - 1) * (2 - (C j k : ℤ)) = 0 := by
    have e : ∀ k, ((C i k : ℤ) - 1) * (2 - (C j k : ℤ))
        = 2 * (C i k : ℤ) - (C i k : ℤ) * (C j k : ℤ) + (C j k : ℤ) - 2 := by
      intro k; ring
    simp only [e]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, hcard7, hA, hB, hR]
    norm_num
  have hzero2 : ∑ k ∈ univ \ ({i, j} : Finset (Fin 9)),
      ((C j k : ℤ) - 1) * (2 - (C i k : ℤ)) = 0 := by
    have e : ∀ k, ((C j k : ℤ) - 1) * (2 - (C i k : ℤ))
        = 2 * (C j k : ℤ) - (C i k : ℤ) * (C j k : ℤ) + (C i k : ℤ) - 2 := by
      intro k; ring
    simp only [e]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, hcard7, hA, hB, hR]
    norm_num
  have hnn1 : ∀ k ∈ univ \ ({i, j} : Finset (Fin 9)),
      0 ≤ ((C i k : ℤ) - 1) * (2 - (C j k : ℤ)) := by
    intro k hk
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hk
    rcases hvi k hk.1 with h1 | h1 <;> rcases hvj k hk.2 with h2 | h2 <;>
      rw [h1, h2] <;> norm_num
  have hnn2 : ∀ k ∈ univ \ ({i, j} : Finset (Fin 9)),
      0 ≤ ((C j k : ℤ) - 1) * (2 - (C i k : ℤ)) := by
    intro k hk
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hk
    rcases hvi k hk.1 with h1 | h1 <;> rcases hvj k hk.2 with h2 | h2 <;>
      rw [h1, h2] <;> norm_num
  have hp1 := (Finset.sum_eq_zero_iff_of_nonneg hnn1).mp hzero1
  have hp2 := (Finset.sum_eq_zero_iff_of_nonneg hnn2).mp hzero2
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hki : k = i
  · subst hki; rw [hi, hji1]; norm_num
  by_cases hkj : k = j
  · subst hkj; rw [hj, hij1]; norm_num
  have hmem : k ∈ univ \ ({i, j} : Finset (Fin 9)) := by
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    exact ⟨hki, hkj⟩
  have e1 := hp1 k hmem
  have e2 := hp2 k hmem
  constructor
  · intro h
    rcases mul_eq_zero.mp e1 with h' | h'
    · rw [h] at h'; norm_num at h'
    · omega
  · intro h
    rcases mul_eq_zero.mp e2 with h' | h'
    · rw [h] at h'; norm_num at h'
    · omega

end Pairs

end Wil24

namespace Wil24

variable {C : Matrix (Fin 9) (Fin 9) ℕ}

section Main
variable (hs : ∀ i j, C i j = C j i) (hr : ∀ i, ∑ j, C i j = 14)
  (hq : ∀ i j, (∑ k, C i k * C k j) + C i j = (if i = j then 12 else 0) + 22)
  (hd : ∀ i, C i i = 0 ∨ C i i = 2 ∨ C i i = 4)

include hs hq in
lemma row_count (x : Fin 9) (f : ℕ → ℤ) :
    ∑ v ∈ Finset.range 6,
        ((((univ.erase x).filter (fun k => C x k = v)).card : ℤ)) * f v
      = ∑ k ∈ univ.erase x, f (C x k) := by
  classical
  have hmaps : ∀ k ∈ univ.erase x, C x k ∈ Finset.range 6 := by
    intro k _
    rw [Finset.mem_range]
    have h := entry_le hs hq x k
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun k => f (C x k))]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  have hcg : ∀ k ∈ (univ.erase x).filter (fun k => C x k = v), f (C x k) = f v := by
    intro k hk
    rw [(Finset.mem_filter.mp hk).2]
  rw [Finset.sum_congr rfl hcg, Finset.sum_const, nsmul_eq_mul]

include hs hr hq in
lemma sq2_erase (x : Fin 9) :
    ∑ k ∈ univ.erase x, ((C x k : ℤ) - 2)^2
      = 3 * (C x x : ℤ) + 10 - (C x x : ℤ)^2 := by
  have hcard : (univ.erase x).card = 8 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ x)]; simp
  have e : ∀ k, ((C x k : ℤ) - 2)^2 = ((C x k : ℤ))^2 - 4 * (C x k : ℤ) + 4 := by
    intro k; ring
  simp only [e]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    hcard, rowErase hr x, sqErase hs hq x]
  push_cast
  ring

include hs hr hq hd in
/-- **There is no Wilbrink orbit matrix of trace `24`.** -/
theorem no24 (htr : ∑ i, C i i = 24) : False := by
  classical
  set S4 : Finset (Fin 9) := univ.filter (fun i => C i i = 4) with hS4def
  have hmemS4 : ∀ i, i ∈ S4 ↔ C i i = 4 := by
    intro i; rw [hS4def]; simp
  have hcardsd : (univ \ S4).card = 9 - S4.card := by
    rw [Finset.card_sdiff, Finset.inter_univ]
    simp
  have hsplit : ∀ T : Finset (Fin 9),
      (∑ i ∈ univ \ T, C i i) + (∑ i ∈ T, C i i) = ∑ i, C i i :=
    fun T => Finset.sum_sdiff (Finset.subset_univ T)
  have hS4sum : ∑ i ∈ S4, C i i = 4 * S4.card := by
    rw [Finset.sum_congr rfl (fun i hi => (hmemS4 i).mp hi), Finset.sum_const]
    ring
  have hOutle : ∀ i ∈ univ \ S4, C i i ≤ 2 := by
    intro i hi
    have h4 : C i i ≠ 4 := fun h => (Finset.mem_sdiff.mp hi).2 ((hmemS4 i).mpr h)
    rcases hd i with h | h | h <;> omega
  have hp3 : 3 ≤ S4.card := by
    have h1 : ∑ i ∈ univ \ S4, C i i ≤ 2 * (9 - S4.card) := by
      calc ∑ i ∈ univ \ S4, C i i ≤ ∑ _i ∈ univ \ S4, 2 := Finset.sum_le_sum hOutle
        _ = (univ \ S4).card * 2 := by rw [Finset.sum_const]; ring
        _ = 2 * (9 - S4.card) := by rw [hcardsd]; ring
    have h2 := hsplit S4
    rw [htr, hS4sum] at h2
    omega
  obtain ⟨i0, hi0⟩ := Finset.card_pos.mp (show 0 < S4.card by omega)
  have hi0d : C i0 i0 = 4 := (hmemS4 i0).mp hi0
  obtain ⟨-, hc0⟩ := four_row hs hr hq hi0d
  obtain ⟨x, y, hxy, hP⟩ := Finset.card_eq_two.mp hc0
  have hmemP : ∀ k, C i0 k = 2 ↔ (k = x ∨ k = y) := by
    intro k
    constructor
    · intro h
      have hk : k ∈ univ.filter (fun k => C i0 k = 2) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ k, h⟩
      rw [hP] at hk
      simpa using hk
    · intro h
      have hk : k ∈ ({x, y} : Finset (Fin 9)) := by simpa using h
      rw [← hP] at hk
      exact (Finset.mem_filter.mp hk).2
  have hall : ∀ i ∈ S4, C i x = 2 ∧ C i y = 2 := by
    intro i hi
    have hid : C i i = 4 := (hmemS4 i).mp hi
    have hfe : univ.filter (fun k => C i k = 2) = univ.filter (fun k => C i0 k = 2) := by
      by_cases h : i = i0
      · rw [h]
      · exact pair_supp hs hr hq hid hi0d h
    constructor
    · have hm : x ∈ univ.filter (fun k => C i k = 2) := by rw [hfe, hP]; simp
      exact (Finset.mem_filter.mp hm).2
    · have hm : y ∈ univ.filter (fun k => C i k = 2) := by rw [hfe, hP]; simp
      exact (Finset.mem_filter.mp hm).2
  have hout : ∀ z : Fin 9, C i0 z = 2 → z ∉ S4 := by
    intro z hz hzS4
    have hzne : z ≠ i0 := by rintro rfl; omega
    have h1 := pair_one hs hr hq hi0d ((hmemS4 z).mp hzS4) (Ne.symm hzne)
    omega
  have hxout : x ∉ S4 := hout x ((hmemP x).mpr (Or.inl rfl))
  have hyout : y ∉ S4 := hout y ((hmemP y).mpr (Or.inr rfl))
  have hrowarg : ∀ z : Fin 9, z ∉ S4 → (∀ i ∈ S4, C i z = 2) →
      C z z = 0 ∧ S4.card ≤ 4 := by
    intro z hz hzall
    obtain ⟨n, hn⟩ : ∃ n : ℕ → ℕ,
        ∀ v, n v = ((univ.erase z).filter (fun k => C z k = v)).card :=
      ⟨_, fun _ => rfl⟩
    have e0 : ∑ v ∈ Finset.range 6, ((n v : ℤ)) * 1 = 8 := by
      simp only [hn]
      rw [row_count hs hq z (fun _ => 1), Finset.sum_const,
        Finset.card_erase_of_mem (Finset.mem_univ z)]
      simp
    have e1 : ∑ v ∈ Finset.range 6, ((n v : ℤ)) * (v : ℤ) = 14 - (C z z : ℤ) := by
      simp only [hn]
      rw [row_count hs hq z (fun v => (v : ℤ)), rowErase hr z]
    have e2 : ∑ v ∈ Finset.range 6, ((n v : ℤ)) * (((v : ℤ)) - 2)^2
        = 3 * (C z z : ℤ) + 10 - (C z z : ℤ)^2 := by
      simp only [hn]
      rw [row_count hs hq z (fun v => ((v : ℤ) - 2)^2), sq2_erase hs hr hq z]
    have hsub : S4 ⊆ (univ.erase z).filter (fun k => C z k = 2) := by
      intro i hi
      have hiz : i ≠ z := fun h => hz (h ▸ hi)
      refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hiz, Finset.mem_univ i⟩, ?_⟩
      rw [hs z i]
      exact hzall i hi
    have hn2 : S4.card ≤ n 2 := by rw [hn 2]; exact Finset.card_le_card hsub
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at e0 e1 e2
    norm_num at e0 e1 e2
    have hzd : C z z = 0 ∨ C z z = 2 := by
      rcases hd z with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd ((hmemS4 z).mpr h) hz
    rcases hzd with h | h
    · rw [h] at e1 e2
      norm_num at e1 e2
      refine ⟨h, ?_⟩
      rcases Nat.eq_zero_or_pos (n 4) with h4 | h4 <;>
        rcases Nat.eq_zero_or_pos (n 5) with h5 | h5 <;> omega
    · rw [h] at e1 e2
      norm_num at e1 e2
      exfalso
      rcases Nat.eq_zero_or_pos (n 4) with h4 | h4 <;>
        rcases Nat.eq_zero_or_pos (n 5) with h5 | h5 <;> omega
  obtain ⟨hxd, hple⟩ := hrowarg x hxout (fun i hi => (hall i hi).1)
  obtain ⟨hyd, -⟩ := hrowarg y hyout (fun i hi => (hall i hi).2)
  have hxysub : ({x, y} : Finset (Fin 9)) ⊆ univ \ S4 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxout⟩
    · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hyout⟩
  have hsp2 := Finset.sum_sdiff (f := fun i => C i i) hxysub
  have hxysum : ∑ i ∈ ({x, y} : Finset (Fin 9)), C i i = 0 := by
    rw [Finset.sum_pair hxy, hxd, hyd]
  have hc : ((univ \ S4) \ ({x, y} : Finset (Fin 9))).card = 7 - S4.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hxysub, hcardsd, Finset.card_pair hxy]
    omega
  have hrest : ∑ i ∈ (univ \ S4) \ ({x, y} : Finset (Fin 9)), C i i ≤ 2 * (7 - S4.card) := by
    have hle : ∀ i ∈ (univ \ S4) \ ({x, y} : Finset (Fin 9)), C i i ≤ 2 :=
      fun i hi => hOutle i (Finset.mem_sdiff.mp hi).1
    calc ∑ i ∈ (univ \ S4) \ ({x, y} : Finset (Fin 9)), C i i
        ≤ ∑ _i ∈ (univ \ S4) \ ({x, y} : Finset (Fin 9)), 2 := Finset.sum_le_sum hle
      _ = ((univ \ S4) \ ({x, y} : Finset (Fin 9))).card * 2 := by rw [Finset.sum_const]; ring
      _ = 2 * (7 - S4.card) := by rw [hc]; ring
  have hfin := hsplit S4
  rw [htr, hS4sum] at hfin
  rw [hxysum] at hsp2
  omega

end Main

end Wil24

/-- **There is no Wilbrink orbit matrix of trace 24.** -/
theorem solution
    (C : Matrix (Fin 9) (Fin 9) ℕ) (hsymm : ∀ i j, C i j = C j i)
    (hrow : ∀ i, ∑ j, C i j = 14)
    (hsq : ∀ i j, (∑ k, C i k * C k j) + C i j = (if i = j then 12 else 0) + 22)
    (hdiag : ∀ i, C i i = 0 ∨ C i i = 2 ∨ C i i = 4)
    (htr : (∑ i, C i i) = 24) : False :=
  Wil24.no24 hsymm hrow hsq hdiag htr
