-- Prove2me | solution 1 for F3SubsetSum.theorem_4_19
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-13T21:12:15.498664+00:00
-- url     : https://prove2.me/submissions/e482afe7-419a-4409-b10c-af49defc010f

import Definitions.Def_F3SubsetSum_MonomialShadow
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open F3SubsetSum

section
variable {n : ℕ}
-- Remove one copy of the largest occupied variable.
private noncomputable def slice (A : Finset (Fin n →₀ ℕ)) (j : Fin n) :=
  (shadow A).filter fun b => b + Finsupp.single j 1 ∈ A ∧ ∀ k > j, b k = 0

private lemma lift_mem (A : Finset (Fin n →₀ ℕ)) (j : Fin n) {z : Fin n →₀ ℕ}
    (hz : z ∈ shadow (slice A j)) : z + Finsupp.single j 1 ∈ shadow A := by
  classical
  obtain ⟨b, hb, hz⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
  have hbA := (Finset.mem_filter.mp hb).2.1
  have hi' : b i ≠ 0 := Finsupp.mem_support_iff.mp hi
  refine Finset.mem_biUnion.mpr ⟨b + Finsupp.single j 1, hbA, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨i, Finsupp.mem_support_iff.mpr ?_, ?_⟩
  · simp only [Finsupp.add_apply]
    omega
  · exact (Finsupp.sub_single_one_add hi').symm

private lemma lift_max (A : Finset (Fin n →₀ ℕ)) (j : Fin n) {z : Fin n →₀ ℕ}
    (hz : z ∈ shadow (slice A j)) :
    (z + Finsupp.single j 1 : Fin n →₀ ℕ) j ≠ 0 ∧
      ∀ k > j, (z + Finsupp.single j 1 : Fin n →₀ ℕ) k = 0 := by
  classical
  obtain ⟨b, hb, h⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
  refine ⟨by simp, ?_⟩
  intro k hk
  simp [(Finset.mem_filter.mp hb).2.2 k hk, Finsupp.single_eq_of_ne (ne_of_gt hk)]

private lemma lift_disjoint (A : Finset (Fin n →₀ ℕ)) {i j : Fin n} (hij : i ≠ j)
    {x y : Fin n →₀ ℕ} (hx : x ∈ shadow (slice A i)) (hy : y ∈ shadow (slice A j)) :
    x + Finsupp.single i 1 ≠ y + Finsupp.single j 1 := by
  intro h
  obtain ⟨hxi, hxk⟩ := lift_max A i hx
  obtain ⟨hyj, hyk⟩ := lift_max A j hy
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · apply hyj
    rw [← h]
    exact hxk _ hlt
  · apply hxi
    rw [h]
    exact hyk _ hgt

-- Restoring the removed largest variable preserves the cardinality of a slice.
private noncomputable def restore (j : Fin n) (B : Finset (Fin n →₀ ℕ)) :=
  B.image (fun b => b + Finsupp.single j 1)

private lemma card_restore (j : Fin n) (B : Finset (Fin n →₀ ℕ)) :
    (restore j B).card = B.card :=
  Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h)

private lemma degree_add_one (a : Fin n →₀ ℕ) (j : Fin n) :
    monoDeg (a + Finsupp.single j 1) = monoDeg a + 1 := by
  classical
  simp [monoDeg, Finsupp.add_apply, Finset.sum_add_distrib, Finsupp.single_apply]

private lemma slice_degree (A : Finset (Fin n →₀ ℕ)) (r : ℕ)
    (hA : ∀ a ∈ A, monoDeg a = r + 1) (j : Fin n) :
    ∀ b ∈ slice A j, monoDeg b = r := by
  intro b hb
  have h := hA _ (Finset.mem_filter.mp hb).2.1
  rw [degree_add_one] at h
  omega

private lemma slice_card_le (A : Finset (Fin n →₀ ℕ)) (j : Fin n) :
    (slice A j).card ≤ (shadow A).card :=
  Finset.card_le_card (Finset.filter_subset _ _)

-- Every positive-degree monomial is recovered from its largest occupied coordinate.
private lemma card_le_sum_slices (A : Finset (Fin n →₀ ℕ))
    (hpos : ∀ a ∈ A, 0 < monoDeg a) :
    A.card ≤ ∑ j, (slice A j).card := by
  classical
  have hsub : A ⊆ Finset.univ.biUnion (fun j => restore j (slice A j)) := by
    intro a ha
    have hne : a ≠ 0 := by
      rintro rfl
      simpa [monoDeg] using hpos _ ha
    have hs := Finsupp.support_nonempty_iff.mpr hne
    let j := a.support.max' hs
    have hj : j ∈ a.support := a.support.max'_mem hs
    have hjle : Finsupp.single j 1 ≤ a :=
      Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj))
    let b := a - Finsupp.single j 1
    have hb : b + Finsupp.single j 1 = a := tsub_add_cancel_of_le hjle
    refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_image.mpr ⟨b, ?_, hb⟩⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩, hb ▸ ha, ?_⟩
    intro k hk
    have hka : a k = 0 := Finsupp.notMem_support_iff.mp (fun h => (not_lt_of_ge (a.support.le_max' k h)) hk)
    simp [b, hka]
  calc
    A.card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ j, (restore j (slice A j)).card := Finset.card_biUnion_le
    _ = _ := by simp only [card_restore]

-- In the shadow, restoring the largest variable separates the slice shadows.
private lemma sum_shadows_le (A : Finset (Fin n →₀ ℕ)) :
    ∑ j, (shadow (slice A j)).card ≤ (shadow A).card := by
  classical
  let B := fun j => restore j (shadow (slice A j))
  have hd : (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint B := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro w hi hj
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hj
    exact lift_disjoint A hij hx hy heq.symm
  have hsub : Finset.univ.biUnion B ⊆ shadow A := by
    intro w hw
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hj
    exact lift_mem A j hx
  calc
    (∑ j, (shadow (slice A j)).card) = ∑ j, (B j).card := by simp only [B, card_restore]
    _ = (Finset.univ.biUnion B).card := (Finset.card_biUnion hd).symm
    _ ≤ _ := Finset.card_le_card hsub
end

-- Multiply the inductive bound for a slice by the missing power.
private lemma slice_weight {r m x b : ℝ} (hr : 0 < r) (hx : 0 ≤ x) (hxm : x ≤ m)
    (hxb : x ^ (1 - 1 / r) ≤ b) : x ≤ m ^ (1 / r) * b := by
  calc
    x = x ^ (1 / r) * x ^ (1 - 1 / r) := by
      rw [← Real.rpow_add' hx (by ring_nf; norm_num), add_sub_cancel, Real.rpow_one]
    _ ≤ m ^ (1 / r) * b :=
      mul_le_mul (Real.rpow_le_rpow hx hxm (by positivity)) hxb
        (Real.rpow_nonneg hx _) (Real.rpow_nonneg (hx.trans hxm) _)

-- We use nonempty families in the induction so degree one has an inhabited shadow.
private theorem positive_degree_bound (n r : ℕ) (hr : 1 ≤ r)
    (A : Finset (Fin n →₀ ℕ)) (hA : ∀ a ∈ A, monoDeg a = r) (hne : A.Nonempty) :
    (A.card : ℝ) ^ (1 - 1 / (r : ℝ)) ≤ (shadow A).card := by
  classical
  induction r, hr using Nat.le_induction generalizing A with
  | base =>
    obtain ⟨a, ha⟩ := hne
    have hneA : a ≠ 0 := by
      rintro rfl
      simpa [monoDeg] using hA _ ha
    obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hneA
    have hsh : (shadow A).Nonempty :=
      ⟨_, Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩⟩
    simpa only [Nat.cast_one, div_one, sub_self, Real.rpow_zero] using
      (show (1 : ℝ) ≤ (shadow A).card by exact_mod_cast Nat.succ_le_of_lt hsh.card_pos)
  | succ r hr ih =>
    let m : ℝ := (shadow A).card
    have hm : 0 ≤ m := Nat.cast_nonneg _
    have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hrpos : (0 : ℝ) < r := by linarith
    have pieces (j : Fin n) : ((slice A j).card : ℝ) ≤
        m ^ (1 / (r : ℝ)) * ((shadow (slice A j)).card : ℝ) := by
      by_cases hj : (slice A j).Nonempty
      · apply slice_weight hrpos (Nat.cast_nonneg _)
        · dsimp only [m]
          exact_mod_cast slice_card_le A j
        · exact ih _ (slice_degree A r hA j) hj
      · rw [Finset.not_nonempty_iff_eq_empty.mp hj]
        simp [shadow]
    have upper : (A.card : ℝ) ≤ m ^ (1 / (r : ℝ) + 1) := by
      calc
        (A.card : ℝ) ≤ ∑ j, ((slice A j).card : ℝ) := by
          exact_mod_cast card_le_sum_slices A (fun a ha => by rw [hA a ha]; omega)
        _ ≤ ∑ j, m ^ (1 / (r : ℝ)) * ((shadow (slice A j)).card : ℝ) :=
          Finset.sum_le_sum (fun j _ => pieces j)
        _ = m ^ (1 / (r : ℝ)) * ∑ j, ((shadow (slice A j)).card : ℝ) := by rw [Finset.mul_sum]
        _ ≤ m ^ (1 / (r : ℝ)) * m := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hm _)
          dsimp only [m]
          exact_mod_cast sum_shadows_le A
        _ = m ^ (1 / (r : ℝ) + 1) := by
          rw [Real.rpow_add' hm (by positivity), Real.rpow_one]
    have hden : 0 < (r : ℝ) + 1 := by positivity
    have hexp : 0 ≤ 1 - 1 / ((r : ℝ) + 1) := by
      rw [sub_nonneg, div_le_one hden]
      linarith
    have hmul : (1 / (r : ℝ) + 1) * (1 - 1 / ((r : ℝ) + 1)) = 1 := by
      field_simp
      ring
    rw [Nat.cast_succ]
    calc
      _ ≤ (m ^ (1 / (r : ℝ) + 1)) ^ (1 - 1 / ((r : ℝ) + 1)) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) upper hexp
      _ = m := by rw [← Real.rpow_mul hm, hmul, Real.rpow_one]

theorem solution (n r : ℕ) (hr : 2 ≤ r) (𝒜 : Finset (Fin n →₀ ℕ))
    (h𝒜 : ∀ α ∈ 𝒜, monoDeg α = r) :
    (𝒜.card : ℝ) ^ (1 - 1 / (r : ℝ)) ≤ (shadow 𝒜).card := by
  classical
  by_cases h : 𝒜.Nonempty
  · exact positive_degree_bound n r (by omega) 𝒜 h𝒜 h
  · have hr' : (1 : ℝ) < r := by exact_mod_cast (show 1 < r by omega)
    have hpos : 0 < 1 - 1 / (r : ℝ) := by
      rw [sub_pos, div_lt_one (by linarith)]
      exact hr'
    rw [Finset.not_nonempty_iff_eq_empty.mp h]
    simp only [Finset.card_empty, Nat.cast_zero, Real.zero_rpow hpos.ne']
    exact Nat.cast_nonneg _
