-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux18_local_negative_mark_collision
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:06:06.817769+00:00
-- url     : https://prove2.me/submissions/fe3985a3-e812-4f6e-af2f-4841a8907628

import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_avram_redux18_finite_mark_product_collision
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-! Only the finitely selected original jump marks need be nonpositive. -/
theorem solution
    {α : Type*} [DecidableEq α] (s : Finset α) (y : α → ℝ)
    (hy : ∀ i, i ∈ s → y i ≤ 0) :
    0 ≤ Real.exp (∑ i ∈ s, y i) -
      (1 - ∑ i ∈ s, (1 - Real.exp (y i))) ∧
    2 * (Real.exp (∑ i ∈ s, y i) -
      (1 - ∑ i ∈ s, (1 - Real.exp (y i)))) ≤
      (s.card : ℝ) * ((s.card : ℝ) - 1) := by
  classical
  let q : α → ℝ := fun i => if i ∈ s then Real.exp (y i) else 1
  have hq0 (i : α) : 0 ≤ q i := by
    by_cases hi : i ∈ s
    · simpa [q, hi] using le_of_lt (Real.exp_pos (y i))
    · simp [q, hi]
  have hq1 (i : α) : q i ≤ 1 := by
    by_cases hi : i ∈ s
    · simpa [q, hi] using (Real.exp_le_one_iff).mpr (hy i hi)
    · simp [q, hi]
  have hp : (∏ i ∈ s, q i) = ∏ i ∈ s, Real.exp (y i) := by
    apply Finset.prod_congr rfl
    intro i hi
    simp [q, hi]
  have hs : (∑ i ∈ s, (1 - q i)) =
      ∑ i ∈ s, (1 - Real.exp (y i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [q, hi]
  have h := AvramDividend.Classical.avram_redux18_finite_mark_product_collision
    s q hq0 hq1
  rw [hp, hs] at h
  simpa only [Real.exp_sum] using h
