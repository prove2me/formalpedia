-- Prove2me | solution 1 for Conway99.no_orbit_matrix_ten_of_exists_four
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T15:38:53.486651+00:00
-- url     : https://prove2.me/submissions/d9f98893-125a-4d45-b6d7-d8e2e513f50d

import Mathlib

open Finset

namespace C99Ten

variable {C : Matrix (Fin 9) (Fin 9) ℕ}

/-- Integer-valued shadow of the orbit matrix. -/
local notation "D" => fun (i j : Fin 9) => ((C i j : ℤ))

section Base
variable (hs : ∀ i j, C i j = C j i) (hr : ∀ i, ∑ j, C i j = 14)
  (hq : ∀ i j, (∑ k, C i k * C k j) + C i j = (if i = j then 12 else 0) + 22)

include hr in
lemma rowZ (i : Fin 9) : ∑ k, ((C i k : ℤ)) = 14 := by
  have h : ((∑ k, C i k : ℕ) : ℤ) = ((14 : ℕ) : ℤ) := by rw [hr i]
  push_cast at h; exact h

include hs hq in
lemma sqZ (i : Fin 9) : ∑ k, ((C i k : ℤ)) ^ 2 = 34 - (C i i : ℤ) := by
  have h := hq i i
  rw [if_pos rfl] at h
  have h2 : ∑ k, C i k * C i k = ∑ k, C i k * C k i :=
    Finset.sum_congr rfl fun k _ => by rw [hs k i]
  have h3 : ((∑ k, C i k * C i k : ℕ) : ℤ) + ((C i i : ℕ) : ℤ) = ((34 : ℕ) : ℤ) := by
    rw [← Nat.cast_add, h2, h]
  push_cast at h3
  have h4 : ∑ k, ((C i k : ℤ)) ^ 2 = ∑ k, ((C i k : ℤ)) * ((C i k : ℤ)) :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [h4]; linarith

include hs hq in
lemma offZ {i j : Fin 9} (hij : i ≠ j) :
    ∑ k, ((C i k : ℤ)) * ((C j k : ℤ)) = 22 - (C i j : ℤ) := by
  have h := hq i j
  rw [if_neg hij] at h
  have h2 : ∑ k, C i k * C j k = ∑ k, C i k * C k j :=
    Finset.sum_congr rfl fun k _ => by rw [hs k j]
  have h3 : ((∑ k, C i k * C j k : ℕ) : ℤ) + ((C i j : ℕ) : ℤ) = ((0 + 22 : ℕ) : ℤ) := by
    rw [← Nat.cast_add, h2, h]
  push_cast at h3; linarith

include hs hq in
lemma entryLe (i j : Fin 9) : (C i j : ℤ) ≤ 5 := by
  by_contra hc
  push_neg at hc
  have hle : ((C i j : ℤ)) ^ 2 ≤ ∑ k, ((C i k : ℤ)) ^ 2 :=
    Finset.single_le_sum (f := fun k => ((C i k : ℤ)) ^ 2) (fun k _ => sq_nonneg _)
      (Finset.mem_univ j)
  rw [sqZ hs hq i] at hle
  have hdnn : (0 : ℤ) ≤ (C i i : ℤ) := by positivity
  nlinarith

end Base


section Row
variable (hs : ∀ i j, C i j = C j i) (hr : ∀ i, ∑ j, C i j = 14)
  (hq : ∀ i j, (∑ k, C i k * C k j) + C i j = (if i = j then 12 else 0) + 22)

include hs hr hq in
/-- A row whose diagonal entry is `4` has every off-diagonal entry in `{1,2}`,
and exactly two of them equal `2`. -/
lemma four_row {i : Fin 9} (hi : C i i = 4) :
    (∀ k, k ≠ i → C i k = 1 ∨ C i k = 2) ∧
      (univ.filter (fun k => C i k = 2)).card = 2 := by
  classical
  have hcard : (univ.erase i).card = 8 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i)]; simp
  have hsum := rowZ hr i
  have hsq := sqZ hs hq i
  have hd : ((C i i : ℤ)) = 4 := by rw [hi]; norm_num
  have h1 : ∑ k ∈ univ.erase i, ((C i k : ℤ)) = 10 := by
    have := Finset.add_sum_erase univ (fun k => ((C i k : ℤ))) (Finset.mem_univ i)
    rw [hsum] at this; linarith [this, hd]
  have h2 : ∑ k ∈ univ.erase i, ((C i k : ℤ)) ^ 2 = 14 := by
    have h := Finset.add_sum_erase univ (fun k => ((C i k : ℤ)) ^ 2) (Finset.mem_univ i)
    rw [hsq, hd] at h
    linarith [h]
  have h3 : ∑ k ∈ univ.erase i, (((C i k : ℤ)) - 1) * (((C i k : ℤ)) - 2) = 0 := by
    have e : ∀ k : Fin 9, (((C i k : ℤ)) - 1) * (((C i k : ℤ)) - 2)
        = ((C i k : ℤ)) ^ 2 - 3 * ((C i k : ℤ)) + 2 := fun k => by ring
    simp only [e]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      hcard, h1, h2]
    norm_num
  have hnn : ∀ k ∈ univ.erase i, 0 ≤ (((C i k : ℤ)) - 1) * (((C i k : ℤ)) - 2) := by
    intro k _
    rcases (by omega : (C i k : ℤ) ≤ 1 ∨ (2 : ℤ) ≤ (C i k : ℤ)) with h | h <;> nlinarith
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h3
  have hval : ∀ k, k ≠ i → C i k = 1 ∨ C i k = 2 := by
    intro k hk
    have := hzero k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)
    rcases mul_eq_zero.mp this with h | h
    · left; omega
    · right; omega
  refine ⟨hval, ?_⟩
  have hsum1 : ∑ k ∈ univ.erase i, (((C i k : ℤ)) - 1) = 2 := by
    rw [Finset.sum_sub_distrib, h1, Finset.sum_const, hcard]; norm_num
  have hbool : ∑ k ∈ univ.erase i, (if C i k = 2 then (1 : ℤ) else 0) = 2 := by
    rw [← hsum1]
    refine Finset.sum_congr rfl fun k hk => ?_
    rcases hval k (Finset.mem_erase.mp hk).1 with h | h <;> rw [h] <;> norm_num
  have hfil : ((univ.erase i).filter (fun k => C i k = 2))
      = univ.filter (fun k => C i k = 2) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
    exact ⟨fun h => h.2, fun h => ⟨by rintro rfl; omega, h⟩⟩
  rw [Finset.sum_boole] at hbool
  rw [← hfil]
  exact_mod_cast hbool

end Row



section Aux
variable {ι : Type*}

lemma sq_add_self_nonneg (n : ℤ) : 0 ≤ n ^ 2 + n := by
  rcases (by omega : 0 ≤ n ∨ n ≤ -1) with h | h
  · nlinarith
  · nlinarith

lemma sq_sub_self_nonneg (n : ℤ) : 0 ≤ n ^ 2 - n := by
  rcases (by omega : n ≤ 0 ∨ 1 ≤ n) with h | h
  · nlinarith
  · nlinarith

/-- Integers whose squares and values have opposite total mass are `0` or `-1`. -/
lemma mem_zero_negOne {S : Finset ι} {g : ι → ℤ}
    (h : ∑ l ∈ S, ((g l) ^ 2 + g l) = 0) : ∀ l ∈ S, g l = 0 ∨ g l = -1 := by
  have hnn : ∀ l ∈ S, 0 ≤ (g l) ^ 2 + g l := fun l _ => sq_add_self_nonneg (g l)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h
  intro l hl
  have h0 := hz l hl
  have hm : g l * (g l + 1) = 0 := by nlinarith [h0]
  rcases mul_eq_zero.mp hm with h' | h'
  · exact Or.inl h'
  · exact Or.inr (by omega)

lemma mem_zero_one {S : Finset ι} {g : ι → ℤ}
    (h : ∑ l ∈ S, ((g l) ^ 2 - g l) = 0) : ∀ l ∈ S, g l = 0 ∨ g l = 1 := by
  have hnn : ∀ l ∈ S, 0 ≤ (g l) ^ 2 - g l := fun l _ => sq_sub_self_nonneg (g l)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h
  intro l hl
  have h0 := hz l hl
  have hm : g l * (g l - 1) = 0 := by nlinarith [h0]
  rcases mul_eq_zero.mp hm with h' | h'
  · exact Or.inl h'
  · exact Or.inr (by omega)

lemma no_seven (u v w : ℤ) (hu : -2 ≤ u) (hv : -2 ≤ v) (hw : -2 ≤ w)
    (hsum : u + v + w = -1) (hsq : u ^ 2 + v ^ 2 + w ^ 2 = 7) : False := by
  simp only [pow_two] at hsq
  have hu2 : u ≤ 2 := by nlinarith
  have hv2 : v ≤ 2 := by nlinarith
  have hww : w = -1 - u - v := by linarith
  subst hww
  interval_cases u <;> interval_cases v <;> omega

lemma pblock (d u v QP QN : ℤ) (hdd : d = 0 ∨ d = 2 ∨ d = 4)
    (hu : -2 ≤ u) (hv : -2 ≤ v)
    (hsum : (d - 2) + u + v = -2)
    (hQP : (d - 2) ^ 2 + u ^ 2 + v ^ 2 = QP)
    (hQN0 : 0 ≤ QN) (hQN7 : QN ≠ 7) (htot : QP + QN = 11 - d) :
    (u = 0 ∧ v = -2) ∨ (u = -2 ∧ v = 0) ∨ (u = 1 ∧ v = -1) ∨ (u = -1 ∧ v = 1) := by
  simp only [pow_two] at hQP
  have hvv : v = -2 - (d - 2) - u := by linarith
  subst hvv
  rcases hdd with rfl | rfl | rfl <;>
    (have hub : u ≤ 2 := by omega) <;>
    interval_cases u <;> omega

end Aux

section Main
variable (hs : ∀ i j, C i j = C j i) (hr : ∀ i, ∑ j, C i j = 14)
  (hq : ∀ i j, (∑ k, C i k * C k j) + C i j = (if i = j then 12 else 0) + 22)
  (hd : ∀ i, C i i = 0 ∨ C i i = 2 ∨ C i i = 4)

include hs hr hq in
/-- The whole structure hanging off a diagonal `4`. -/
lemma setup {i0 : Fin 9} (hi0 : C i0 i0 = 4) :
    ∃ x y : Fin 9, x ≠ y ∧ x ≠ i0 ∧ y ≠ i0 ∧
      C i0 x = 2 ∧ C i0 y = 2 ∧
      (∀ k, k ≠ i0 → k ≠ x → k ≠ y → C i0 k = 1) := by
  classical
  obtain ⟨hval, hc⟩ := four_row hs hr hq hi0
  obtain ⟨x, y, hxy, hP⟩ := Finset.card_eq_two.mp hc
  have hmem : ∀ k, C i0 k = 2 ↔ (k = x ∨ k = y) := by
    intro k
    constructor
    · intro h
      have hk : k ∈ univ.filter (fun k => C i0 k = 2) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ k, h⟩
      rw [hP] at hk; simpa using hk
    · intro h
      have hk : k ∈ ({x, y} : Finset (Fin 9)) := by simpa using h
      rw [← hP] at hk
      exact (Finset.mem_filter.mp hk).2
  have hx2 : C i0 x = 2 := (hmem x).mpr (Or.inl rfl)
  have hy2 : C i0 y = 2 := (hmem y).mpr (Or.inr rfl)
  refine ⟨x, y, hxy, ?_, ?_, hx2, hy2, ?_⟩
  · rintro rfl; omega
  · rintro rfl; omega
  · intro k hk hkx hky
    rcases hval k hk with h | h
    · exact h
    · exact absurd ((hmem k).mp h) (by simpa using ⟨hkx, hky⟩)


include hs hr hq hd in
set_option maxHeartbeats 2000000 in
theorem ten_exists_four (htr : (∑ i, C i i) = 10) (hfour : ∃ i, C i i = 4) : False := by
  classical
  obtain ⟨i0, hi0⟩ := hfour
  obtain ⟨x, y, hxy, hxi, hyi, hx2, hy2, hone⟩ := setup hs hr hq hi0
  set T : Finset (Fin 9) := {i0, x, y} with hTdef
  have hi0T : i0 ∉ ({x, y} : Finset (Fin 9)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact fun h => h.elim (fun h => hxi h.symm) (fun h => hyi h.symm)
  have hxT : x ∉ ({y} : Finset (Fin 9)) := by simpa using hxy
  have hcardT : T.card = 3 := by
    rw [hTdef, Finset.card_insert_of_notMem hi0T, Finset.card_insert_of_notMem hxT,
      Finset.card_singleton]
  set R : Finset (Fin 9) := univ \ T with hRdef
  have hcardR : R.card = 6 := by
    rw [hRdef, Finset.card_sdiff, Finset.inter_univ, hcardT] <;> simp [hcardT]
  have hmemR : ∀ k, k ∈ R ↔ (k ≠ i0 ∧ k ≠ x ∧ k ≠ y) := by
    intro k
    simp only [hRdef, hTdef, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or]
  -- the three-element sum over `T`
  have sumT : ∀ f : Fin 9 → ℤ, ∑ k ∈ T, f k = f i0 + f x + f y := by
    intro f
    rw [hTdef, Finset.sum_insert hi0T, Finset.sum_insert hxT, Finset.sum_singleton, add_assoc]
  have splitR : ∀ f : Fin 9 → ℤ, (∑ k ∈ R, f k) + (f i0 + f x + f y) = ∑ k, f k := by
    intro f
    rw [← sumT f, hRdef]
    exact Finset.sum_sdiff (Finset.subset_univ T)
  -- the fundamental row identity for the `4`-row
  have keyrow : ∀ z : Fin 9, ∑ k, ((C i0 k : ℤ)) * ((C z k : ℤ))
      = 14 + 3 * (C z i0 : ℤ) + (C z x : ℤ) + (C z y : ℤ) := by
    intro z
    have hg : ∑ k, (((C i0 k : ℤ)) - 1) * ((C z k : ℤ))
        = ∑ k ∈ T, (((C i0 k : ℤ)) - 1) * ((C z k : ℤ)) := by
      refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro k _ hk
      have hk' : k ≠ i0 ∧ k ≠ x ∧ k ≠ y := by
        rw [hRdef] at hmemR
        have : k ∈ univ \ T := Finset.mem_sdiff.mpr ⟨Finset.mem_univ k, hk⟩
        exact (hmemR k).mp this
      rw [hone k hk'.1 hk'.2.1 hk'.2.2]
      norm_num
    have hT3 := sumT (fun k => (((C i0 k : ℤ)) - 1) * ((C z k : ℤ)))
    have hdec : ∀ k : Fin 9, ((C i0 k : ℤ)) * ((C z k : ℤ))
        = (((C i0 k : ℤ)) - 1) * ((C z k : ℤ)) + ((C z k : ℤ)) := fun k => by ring
    rw [Finset.sum_congr rfl (fun k _ => hdec k), Finset.sum_add_distrib, hg, hT3,
      rowZ hr z, hi0, hx2, hy2]
    push_cast; ring
  -- Step A: the two `2`-neighbours of `i0` have zero diagonal and are non-adjacent.
  have hix : i0 ≠ x := fun h => hxi h.symm
  have hiy : i0 ≠ y := fun h => hyi h.symm
  have hxx : (C x x : ℤ) = 0 ∧ (C x y : ℤ) = 0 := by
    have h := keyrow x
    rw [offZ hs hq hix, hx2] at h
    have hsym : (C x i0 : ℤ) = (C i0 x : ℤ) := by rw [hs x i0]
    rw [hx2] at hsym
    have h1 : (0 : ℤ) ≤ (C x x : ℤ) := by positivity
    have h2 : (0 : ℤ) ≤ (C x y : ℤ) := by positivity
    constructor <;> [skip; skip] <;> push_cast at h <;> omega
  have hyy : (C y y : ℤ) = 0 := by
    have h := keyrow y
    rw [offZ hs hq hiy, hy2] at h
    have hsym : (C y i0 : ℤ) = (C i0 y : ℤ) := by rw [hs y i0]
    rw [hy2] at hsym
    have h1 : (0 : ℤ) ≤ (C y y : ℤ) := by positivity
    have h2 : (0 : ℤ) ≤ (C y x : ℤ) := by positivity
    push_cast at h; omega
  -- Step B: for every other index the two neighbour weights add up to `4`.
  have hsum4 : ∀ j ∈ R, (C j x : ℤ) + (C j y : ℤ) = 4 := by
    intro j hj
    obtain ⟨hj0, hjx, hjy⟩ := (hmemR j).mp hj
    have hij : i0 ≠ j := fun h => hj0 h.symm
    have h := keyrow j
    rw [offZ hs hq hij, hone j hj0 hjx hjy] at h
    have hsym : (C j i0 : ℤ) = (C i0 j : ℤ) := by rw [hs j i0]
    rw [hone j hj0 hjx hjy] at hsym
    push_cast at h; omega
  have hxi0v : (C x i0 : ℤ) = 2 := by rw [hs x i0]; rw [hx2]; norm_num
  have hyi0v : (C y i0 : ℤ) = 2 := by rw [hs y i0]; rw [hy2]; norm_num
  have hji0 : ∀ j ∈ R, (C j i0 : ℤ) = 1 := by
    intro j hj
    obtain ⟨hj0, hjx, hjy⟩ := (hmemR j).mp hj
    rw [hs j i0, hone j hj0 hjx hjy]; norm_num
  have hjx : ∀ j ∈ R, (C j x : ℤ) = (C x j : ℤ) := fun j _ => by rw [hs j x]
  -- Step C: the profile of the row of `x` on `R`.
  have hSa : ∑ j ∈ R, ((C x j : ℤ)) = 12 := by
    have h := splitR (fun k => ((C x k : ℤ)))
    rw [rowZ hr x, hxi0v, hxx.1, hxx.2] at h; linarith
  have hSa2 : ∑ j ∈ R, ((C x j : ℤ)) ^ 2 = 30 := by
    have h := splitR (fun k => ((C x k : ℤ)) ^ 2)
    rw [sqZ hs hq x, hxi0v, hxx.1, hxx.2] at h; norm_num at h; linarith
  -- Step D: the block of `C` on `R`.
  have hrowB : ∀ j ∈ R, ∑ l ∈ R, ((C j l : ℤ)) = 9 := by
    intro j hj
    have h := splitR (fun k => ((C j k : ℤ)))
    rw [rowZ hr j, hji0 j hj] at h
    have := hsum4 j hj
    linarith
  have hsqB : ∀ j ∈ R, ∑ l ∈ R, ((C j l : ℤ)) ^ 2
      = 33 - (C j j : ℤ) - ((C x j : ℤ)) ^ 2 - (4 - ((C x j : ℤ))) ^ 2 := by
    intro j hj
    have h := splitR (fun k => ((C j k : ℤ)) ^ 2)
    rw [sqZ hs hq j, hji0 j hj] at h
    have h4 := hsum4 j hj
    have hjxv := hjx j hj
    have hjyv : (C j y : ℤ) = 4 - ((C x j : ℤ)) := by rw [← hjxv]; linarith
    rw [hjxv, hjyv] at h
    linarith
  have hcrossB : ∀ j ∈ R, ∑ l ∈ R, ((C x l : ℤ)) * ((C j l : ℤ)) = 20 - ((C x j : ℤ)) := by
    intro j hj
    obtain ⟨hj0, hjxne, hjyne⟩ := (hmemR j).mp hj
    have hxj : x ≠ j := fun h => hjxne h.symm
    have h := splitR (fun k => ((C x k : ℤ)) * ((C j k : ℤ)))
    rw [offZ hs hq hxj, hxi0v, hxx.1, hxx.2, hji0 j hj] at h
    linarith
  have htrB : ∑ j ∈ R, ((C j j : ℤ)) = 6 := by
    have h := splitR (fun k => ((C k k : ℤ)))
    have h10 : ∑ k, ((C k k : ℤ)) = 10 := by
      have : ((∑ i, C i i : ℕ) : ℤ) = ((10 : ℕ) : ℤ) := by rw [htr]
      push_cast at this; exact this
    rw [h10, hi0, hxx.1, hyy] at h
    push_cast at h; linarith
  have habd : ∀ j ∈ R, 0 ≤ ((C x j : ℤ)) ∧ ((C x j : ℤ)) ≤ 4 := by
    intro j hj
    have h4 := hsum4 j hj
    have hjxv := hjx j hj
    have h1 : (0 : ℤ) ≤ (C j x : ℤ) := by positivity
    have h2 : (0 : ℤ) ≤ (C j y : ℤ) := by positivity
    omega
  -- Recentre: `c j = C x j - 2` and `e j l = C j l - 2`.
  have hc0 : ∑ j ∈ R, (((C x j : ℤ)) - 2) = 0 := by
    rw [Finset.sum_sub_distrib, hSa, Finset.sum_const, hcardR]; norm_num
  have hc2 : ∑ j ∈ R, (((C x j : ℤ)) - 2) ^ 2 = 6 := by
    have e : ∀ l : Fin 9, (((C x l : ℤ)) - 2) ^ 2
        = ((C x l : ℤ)) ^ 2 - 4 * ((C x l : ℤ)) + 4 := fun l => by ring
    rw [Finset.sum_congr rfl (fun l _ => e l), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, hcardR, hSa, hSa2]
    norm_num
  have heR : ∀ j ∈ R, ∑ l ∈ R, (((C j l : ℤ)) - 2) = -3 := by
    intro j hj
    rw [Finset.sum_sub_distrib, hrowB j hj, Finset.sum_const, hcardR]; norm_num
  have heS : ∀ j ∈ R, ∑ l ∈ R, (((C j l : ℤ)) - 2) ^ 2
      = 13 - 2 * (((C x j : ℤ)) - 2) ^ 2 - ((C j j : ℤ)) := by
    intro j hj
    have e : ∀ l : Fin 9, (((C j l : ℤ)) - 2) ^ 2
        = ((C j l : ℤ)) ^ 2 - 4 * ((C j l : ℤ)) + 4 := fun l => by ring
    rw [Finset.sum_congr rfl (fun l _ => e l), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, hcardR, hsqB j hj, hrowB j hj]
    push_cast; ring
  have heC : ∀ j ∈ R, ∑ l ∈ R, ((((C x l : ℤ)) - 2) * (((C j l : ℤ)) - 2))
      = -(((C x j : ℤ)) - 2) := by
    intro j hj
    have e : ∀ l : Fin 9, (((C x l : ℤ)) - 2) * (((C j l : ℤ)) - 2)
        = ((C x l : ℤ)) * ((C j l : ℤ)) - 2 * ((C x l : ℤ)) - 2 * ((C j l : ℤ)) + 4 :=
      fun l => by ring
    rw [Finset.sum_congr rfl (fun l _ => e l), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, hcardR,
      hcrossB j hj, hSa, hrowB j hj]
    push_cast; ring
  have hcbd : ∀ j ∈ R, -2 ≤ ((C x j : ℤ)) - 2 ∧ ((C x j : ℤ)) - 2 ≤ 2 := by
    intro j hj; have := habd j hj; omega
  by_cases hex : ∃ j0 ∈ R, (((C x j0 : ℤ)) - 2) ^ 2 = 4
  · -- Case 1: some entry of the recentred row of `x` is `±2`.
    obtain ⟨j0, hj0R, hj0c⟩ := hex
    have hE : ∀ f : Fin 9 → ℤ, f j0 + ∑ l ∈ R.erase j0, f l = ∑ l ∈ R, f l :=
      fun f => Finset.add_sum_erase R f hj0R
    have hEc0 : ∑ l ∈ R.erase j0, (((C x l : ℤ)) - 2) = -(((C x j0 : ℤ)) - 2) := by
      have h := hE (fun l => ((C x l : ℤ)) - 2); rw [hc0] at h; linarith
    have hEc2 : ∑ l ∈ R.erase j0, (((C x l : ℤ)) - 2) ^ 2 = 2 := by
      have h := hE (fun l => (((C x l : ℤ)) - 2) ^ 2); rw [hc2, hj0c] at h; linarith
    have hEcle : ∀ l ∈ R.erase j0, (((C x l : ℤ)) - 2) ^ 2 ≤ 1 := by
      intro l hl
      have hlR : l ∈ R := Finset.mem_of_mem_erase hl
      have hle : (((C x l : ℤ)) - 2) ^ 2 ≤ ∑ m ∈ R.erase j0, (((C x m : ℤ)) - 2) ^ 2 :=
        Finset.single_le_sum (f := fun m => (((C x m : ℤ)) - 2) ^ 2)
          (fun m _ => sq_nonneg _) hl
      rw [hEc2] at hle
      have hb := hcbd l hlR
      rcases (by omega : ((C x l : ℤ)) - 2 = -2 ∨ ((C x l : ℤ)) - 2 = -1 ∨
          ((C x l : ℤ)) - 2 = 0 ∨ ((C x l : ℤ)) - 2 = 1 ∨ ((C x l : ℤ)) - 2 = 2) with
        h | h | h | h | h <;> rw [h] at hle ⊢ <;> revert hle <;> norm_num
    have hEcbd : ∀ l ∈ R.erase j0, -1 ≤ ((C x l : ℤ)) - 2 ∧ ((C x l : ℤ)) - 2 ≤ 1 := by
      intro l hl
      have h1 := hEcle l hl
      constructor <;> nlinarith [h1]
    have hj0two : ((C x j0 : ℤ)) - 2 = 2 ∨ ((C x j0 : ℤ)) - 2 = -2 := by
      have hb := hcbd j0 hj0R
      rcases (by omega : ((C x j0 : ℤ)) - 2 = -2 ∨ ((C x j0 : ℤ)) - 2 = -1 ∨
          ((C x j0 : ℤ)) - 2 = 0 ∨ ((C x j0 : ℤ)) - 2 = 1 ∨ ((C x j0 : ℤ)) - 2 = 2) with
        h | h | h | h | h <;> rw [h] at hj0c ⊢ <;> revert hj0c <;> norm_num
    have hEe0 : ((C j0 j0 : ℤ)) - 2 + ∑ l ∈ R.erase j0, (((C j0 l : ℤ)) - 2) = -3 := by
      have h := hE (fun l => ((C j0 l : ℤ)) - 2); rw [heR j0 hj0R] at h; linarith
    have hEe2 : (((C j0 j0 : ℤ)) - 2) ^ 2 + ∑ l ∈ R.erase j0, (((C j0 l : ℤ)) - 2) ^ 2
        = 5 - ((C j0 j0 : ℤ)) := by
      have h := hE (fun l => (((C j0 l : ℤ)) - 2) ^ 2)
      rw [heS j0 hj0R, hj0c] at h; linarith
    have hEec : (((C x j0 : ℤ)) - 2) * (((C j0 j0 : ℤ)) - 2)
        + ∑ l ∈ R.erase j0, ((((C x l : ℤ)) - 2) * (((C j0 l : ℤ)) - 2))
        = -(((C x j0 : ℤ)) - 2) := by
      have h := hE (fun l => (((C x l : ℤ)) - 2) * (((C j0 l : ℤ)) - 2))
      rw [heC j0 hj0R] at h; linarith
    have hsqnn : (0 : ℤ) ≤ ∑ l ∈ R.erase j0, (((C j0 l : ℤ)) - 2) ^ 2 :=
      Finset.sum_nonneg fun l _ => sq_nonneg _
    rcases hd j0 with h0 | h0 | h0
    · -- diagonal `0`
      rw [h0] at hEe0 hEe2 hEec
      push_cast at hEe0 hEe2 hEec
      have hs0 : ∑ l ∈ R.erase j0, (((C j0 l : ℤ)) - 2) = -1 := by linarith
      have hs2 : ∑ l ∈ R.erase j0, (((C j0 l : ℤ)) - 2) ^ 2 = 1 := by linarith
      have hz : ∑ l ∈ R.erase j0, ((((C j0 l : ℤ)) - 2) ^ 2 + (((C j0 l : ℤ)) - 2)) = 0 := by
        rw [Finset.sum_add_distrib, hs0, hs2]; ring
      have he01 := mem_zero_negOne hz
      have hlow : ∑ l ∈ R.erase j0, (((C j0 l : ℤ)) - 2)
          ≤ ∑ l ∈ R.erase j0, ((((C x l : ℤ)) - 2) * (((C j0 l : ℤ)) - 2)) := by
        refine Finset.sum_le_sum fun l hl => ?_
        have hb := hEcbd l hl
        rcases he01 l hl with h | h <;> rw [h] <;> linarith [hb.1, hb.2]
      have hhigh : ∑ l ∈ R.erase j0, ((((C x l : ℤ)) - 2) * (((C j0 l : ℤ)) - 2))
          ≤ ∑ l ∈ R.erase j0, (-(((C j0 l : ℤ)) - 2)) := by
        refine Finset.sum_le_sum fun l hl => ?_
        have hb := hEcbd l hl
        rcases he01 l hl with h | h <;> rw [h] <;> linarith [hb.1, hb.2]
      rw [hs0] at hlow
      rw [Finset.sum_neg_distrib, hs0] at hhigh
      rcases hj0two with h | h <;> rw [h] at hEec <;> linarith
    · -- diagonal `2`
      rw [h0] at hEe0 hEe2 hEec
      push_cast at hEe0 hEe2 hEec
      have hs0 : ∑ l ∈ R.erase j0, (((C j0 l : ℤ)) - 2) = -3 := by linarith
      have hs2 : ∑ l ∈ R.erase j0, (((C j0 l : ℤ)) - 2) ^ 2 = 3 := by linarith
      have hz : ∑ l ∈ R.erase j0, ((((C j0 l : ℤ)) - 2) ^ 2 + (((C j0 l : ℤ)) - 2)) = 0 := by
        rw [Finset.sum_add_distrib, hs0, hs2]; ring
      have he01 := mem_zero_negOne hz
      rcases hj0two with h | h
      · have hzc : ∑ l ∈ R.erase j0, ((((C x l : ℤ)) - 2) ^ 2 + (((C x l : ℤ)) - 2)) = 0 := by
          rw [Finset.sum_add_distrib, hEc0, hEc2, h]; ring
        have hc01 := mem_zero_negOne hzc
        have hnn : (0 : ℤ) ≤ ∑ l ∈ R.erase j0,
            ((((C x l : ℤ)) - 2) * (((C j0 l : ℤ)) - 2)) := by
          refine Finset.sum_nonneg fun l hl => ?_
          rcases hc01 l hl with hcc | hcc <;> rcases he01 l hl with hee | hee <;>
            rw [hcc, hee] <;> norm_num
        rw [h] at hEec; linarith
      · have hzc : ∑ l ∈ R.erase j0, ((((C x l : ℤ)) - 2) ^ 2 - (((C x l : ℤ)) - 2)) = 0 := by
          rw [Finset.sum_sub_distrib, hEc0, hEc2, h]; ring
        have hc01 := mem_zero_one hzc
        have hnp : ∑ l ∈ R.erase j0,
            ((((C x l : ℤ)) - 2) * (((C j0 l : ℤ)) - 2)) ≤ 0 := by
          have hcmp : ∑ l ∈ R.erase j0, ((((C x l : ℤ)) - 2) * (((C j0 l : ℤ)) - 2))
              ≤ ∑ _l ∈ R.erase j0, (0 : ℤ) := by
            refine Finset.sum_le_sum fun l hl => ?_
            rcases hc01 l hl with hcc | hcc <;> rcases he01 l hl with hee | hee <;>
              rw [hcc, hee] <;> norm_num
          simpa using hcmp
        rw [h] at hEec; linarith
    · -- diagonal `4` is impossible
      rw [h0] at hEe2
      push_cast at hEe2
      linarith
  · -- Case 2: every recentred entry of the row of `x` on `R` is `±1`.
    push_neg at hex
    have hcase : ∀ j ∈ R, ((C x j : ℤ)) - 2 = -2 ∨ ((C x j : ℤ)) - 2 = -1 ∨
        ((C x j : ℤ)) - 2 = 0 ∨ ((C x j : ℤ)) - 2 = 1 ∨ ((C x j : ℤ)) - 2 = 2 := by
      intro j hj; have := hcbd j hj; omega
    have hle : ∀ j ∈ R, (((C x j : ℤ)) - 2) ^ 2 ≤ 1 := by
      intro j hj
      have hne := hex j hj
      rcases hcase j hj with h | h | h | h | h <;> rw [h] at hne ⊢ <;> revert hne <;> norm_num
    have hcpm : ∀ j ∈ R, ((C x j : ℤ)) - 2 = 1 ∨ ((C x j : ℤ)) - 2 = -1 := by
      have hz : ∑ j ∈ R, (1 - (((C x j : ℤ)) - 2) ^ 2) = 0 := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, hcardR, hc2]; norm_num
      have hall := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j hj => by linarith [hle j hj])).mp hz
      intro j hj
      have hsq : (((C x j : ℤ)) - 2) ^ 2 = 1 := by have := hall j hj; linarith
      rcases hcase j hj with h | h | h | h | h
      · rw [h] at hsq; norm_num at hsq
      · exact Or.inr h
      · rw [h] at hsq; norm_num at hsq
      · exact Or.inl h
      · rw [h] at hsq; norm_num at hsq
    set P : Finset (Fin 9) := R.filter (fun j => ((C x j : ℤ)) - 2 = 1) with hPdef
    set N : Finset (Fin 9) := R.filter (fun j => ¬ (((C x j : ℤ)) - 2 = 1)) with hNdef
    have hsplitPN : ∀ f : Fin 9 → ℤ, (∑ l ∈ P, f l) + (∑ l ∈ N, f l) = ∑ l ∈ R, f l :=
      fun f => Finset.sum_filter_add_sum_filter_not R _ f
    have hPsub : P ⊆ R := Finset.filter_subset _ _
    have hNsub : N ⊆ R := Finset.filter_subset _ _
    have hPval : ∀ j ∈ P, ((C x j : ℤ)) - 2 = 1 := fun j hj => (Finset.mem_filter.mp hj).2
    have hNval : ∀ j ∈ N, ((C x j : ℤ)) - 2 = -1 := by
      intro j hj
      obtain ⟨hjR, hjn⟩ := Finset.mem_filter.mp hj
      rcases hcpm j hjR with h | h
      · exact absurd h hjn
      · exact h
    have hcardPN : (P.card : ℤ) + (N.card : ℤ) = 6 := by
      have h := hsplitPN (fun _ => (1 : ℤ))
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
      rw [hcardR] at h
      exact_mod_cast h
    have hdiff : (P.card : ℤ) - (N.card : ℤ) = 0 := by
      have h := hsplitPN (fun l => ((C x l : ℤ)) - 2)
      rw [hc0] at h
      have hP1 : ∑ l ∈ P, (((C x l : ℤ)) - 2) = (P.card : ℤ) := by
        rw [Finset.sum_congr rfl (fun l hl => hPval l hl)]
        simp
      have hN1 : ∑ l ∈ N, (((C x l : ℤ)) - 2) = -(N.card : ℤ) := by
        rw [Finset.sum_congr rfl (fun l hl => hNval l hl)]
        simp
      rw [hP1, hN1] at h
      linarith
    have hPcard : P.card = 3 := by omega
    have hNcard : N.card = 3 := by omega
    obtain ⟨p1, p2, p3, hp12, hp13, hp23, hPeq⟩ := Finset.card_eq_three.mp hPcard
    obtain ⟨n1, n2, n3, hn12, hn13, hn23, hNeq⟩ := Finset.card_eq_three.mp hNcard
    have sumP : ∀ f : Fin 9 → ℤ, ∑ l ∈ P, f l = f p1 + f p2 + f p3 := by
      intro f
      rw [hPeq, Finset.sum_insert (by simp [hp12, hp13]),
        Finset.sum_insert (by simp [hp23]), Finset.sum_singleton, add_assoc]
    have sumN : ∀ f : Fin 9 → ℤ, ∑ l ∈ N, f l = f n1 + f n2 + f n3 := by
      intro f
      rw [hNeq, Finset.sum_insert (by simp [hn12, hn13]),
        Finset.sum_insert (by simp [hn23]), Finset.sum_singleton, add_assoc]
    have hSPN : ∀ j ∈ R, (∑ l ∈ P, (((C j l : ℤ)) - 2))
        + (∑ l ∈ N, (((C j l : ℤ)) - 2)) = -3 := by
      intro j hj; rw [hsplitPN (fun l => ((C j l : ℤ)) - 2)]; exact heR j hj
    have hCross : ∀ j ∈ R,
        (∑ l ∈ P, (((C j l : ℤ)) - 2)) - (∑ l ∈ N, (((C j l : ℤ)) - 2))
          = -(((C x j : ℤ)) - 2) := by
      intro j hj
      have h := hsplitPN (fun l => (((C x l : ℤ)) - 2) * (((C j l : ℤ)) - 2))
      rw [heC j hj] at h
      have hP1 : ∑ l ∈ P, ((((C x l : ℤ)) - 2) * (((C j l : ℤ)) - 2))
          = ∑ l ∈ P, (((C j l : ℤ)) - 2) :=
        Finset.sum_congr rfl (fun l hl => by rw [hPval l hl]; ring)
      have hN1 : ∑ l ∈ N, ((((C x l : ℤ)) - 2) * (((C j l : ℤ)) - 2))
          = -∑ l ∈ N, (((C j l : ℤ)) - 2) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun l hl => by rw [hNval l hl]; ring)
      rw [hP1, hN1] at h
      linarith [h]
    have hQtot : ∀ j ∈ R, (∑ l ∈ P, (((C j l : ℤ)) - 2) ^ 2)
        + (∑ l ∈ N, (((C j l : ℤ)) - 2) ^ 2) = 11 - ((C j j : ℤ)) := by
      intro j hj
      rw [hsplitPN (fun l => (((C j l : ℤ)) - 2) ^ 2), heS j hj]
      have hcj : (((C x j : ℤ)) - 2) ^ 2 = 1 := by
        rcases hcpm j hj with h | h <;> rw [h] <;> norm_num
      rw [hcj]; ring
    have hem2 : ∀ i k : Fin 9, -2 ≤ ((C i k : ℤ)) - 2 := by
      intro i k
      have : (0 : ℤ) ≤ ((C i k : ℤ)) := by positivity
      omega
    have hdz : ∀ i : Fin 9, ((C i i : ℤ)) = 0 ∨ ((C i i : ℤ)) = 2 ∨ ((C i i : ℤ)) = 4 := by
      intro i; rcases hd i with h | h | h <;> rw [h] <;> norm_num
    have hQNnn : ∀ j : Fin 9, (0 : ℤ) ≤ ∑ l ∈ N, (((C j l : ℤ)) - 2) ^ 2 :=
      fun j => Finset.sum_nonneg fun l _ => sq_nonneg _
    have hProws : ∀ j ∈ P, (∑ l ∈ P, (((C j l : ℤ)) - 2)) = -2
        ∧ (∑ l ∈ N, (((C j l : ℤ)) - 2)) = -1 := by
      intro j hj
      have hjR := hPsub hj
      have h1 := hSPN j hjR
      have h2 := hCross j hjR
      rw [hPval j hj] at h2
      exact ⟨by linarith, by linarith⟩
    have hQN7 : ∀ j ∈ P, (∑ l ∈ N, (((C j l : ℤ)) - 2) ^ 2) ≠ 7 := by
      intro j hj h7
      have hsn := (hProws j hj).2
      rw [sumN] at hsn
      rw [sumN] at h7
      exact no_seven _ _ _ (hem2 j n1) (hem2 j n2) (hem2 j n3) hsn h7
    have hmp1 : p1 ∈ P := by rw [hPeq]; simp
    have hmp2 : p2 ∈ P := by rw [hPeq]; simp
    have hmp3 : p3 ∈ P := by rw [hPeq]; simp
    have step : ∀ j ∈ P, ∀ b c : Fin 9,
        (((C j j : ℤ)) - 2) + (((C j b : ℤ)) - 2) + (((C j c : ℤ)) - 2) = -2 →
        (((C j j : ℤ)) - 2) ^ 2 + (((C j b : ℤ)) - 2) ^ 2 + (((C j c : ℤ)) - 2) ^ 2
            + (∑ l ∈ N, (((C j l : ℤ)) - 2) ^ 2) = 11 - ((C j j : ℤ)) →
        ((((C j b : ℤ)) - 2 = 0 ∧ ((C j c : ℤ)) - 2 = -2) ∨
          (((C j b : ℤ)) - 2 = -2 ∧ ((C j c : ℤ)) - 2 = 0) ∨
          (((C j b : ℤ)) - 2 = 1 ∧ ((C j c : ℤ)) - 2 = -1) ∨
          (((C j b : ℤ)) - 2 = -1 ∧ ((C j c : ℤ)) - 2 = 1)) := by
      intro j hj b c hsum hQ
      exact pblock ((C j j : ℤ)) (((C j b : ℤ)) - 2) (((C j c : ℤ)) - 2)
        ((((C j j : ℤ)) - 2) ^ 2 + (((C j b : ℤ)) - 2) ^ 2 + (((C j c : ℤ)) - 2) ^ 2)
        (∑ l ∈ N, (((C j l : ℤ)) - 2) ^ 2)
        (hdz j) (hem2 j b) (hem2 j c) hsum rfl (hQNnn j) (hQN7 j hj) (by linarith)
    have hd1 := hProws p1 hmp1
    have hd2 := hProws p2 hmp2
    have hd3 := hProws p3 hmp3
    have hq1 := hQtot p1 (hPsub hmp1)
    have hq2 := hQtot p2 (hPsub hmp2)
    have hq3 := hQtot p3 (hPsub hmp3)
    rw [sumP] at hd1 hd2 hd3 hq1 hq2 hq3
    have hs21 : ((C p2 p1 : ℤ)) = ((C p1 p2 : ℤ)) := by rw [hs p2 p1]
    have hs31 : ((C p3 p1 : ℤ)) = ((C p1 p3 : ℤ)) := by rw [hs p3 p1]
    have hs32 : ((C p3 p2 : ℤ)) = ((C p2 p3 : ℤ)) := by rw [hs p3 p2]
    have r1 := step p1 hmp1 p2 p3 (by linarith [hd1.1]) (by linarith [hq1])
    have r2 := step p2 hmp2 p1 p3 (by linarith [hd2.1]) (by linarith [hq2])
    have r3 := step p3 hmp3 p1 p2 (by linarith [hd3.1]) (by linarith [hq3])
    omega


end Main

end C99Ten


/-- **There is no Wilbrink orbit matrix of trace `10` with a diagonal entry `4`.** -/
theorem solution
    (C : Matrix (Fin 9) (Fin 9) ℕ) (hsymm : ∀ i j, C i j = C j i)
    (hrow : ∀ i, ∑ j, C i j = 14)
    (hsq : ∀ i j, (∑ k, C i k * C k j) + C i j = (if i = j then 12 else 0) + 22)
    (hdiag : ∀ i, C i i = 0 ∨ C i i = 2 ∨ C i i = 4)
    (htr : (∑ i, C i i) = 10)
    (hfour : ∃ i, C i i = 4) : False :=
  C99Ten.ten_exists_four hsymm hrow hsq hdiag htr hfour
