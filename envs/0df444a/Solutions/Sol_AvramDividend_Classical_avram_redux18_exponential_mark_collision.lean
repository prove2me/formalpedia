-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux18_exponential_mark_collision
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:45:09.902699+00:00
-- url     : https://prove2.me/submissions/59921208-0dca-4ee7-88d9-419646072cb8

import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_avram_redux18_finite_mark_product_collision
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-! For nonpositive real jump marks, the exponential of their sum differs from
    its linearised marked-jump compensator by at most the number of pairs. -/
theorem solution
    {α : Type*} [DecidableEq α] (s : Finset α) (y : α → ℝ)
    (hy : ∀ i, y i ≤ 0) :
    0 ≤ Real.exp (∑ i ∈ s, y i) -
      (1 - ∑ i ∈ s, (1 - Real.exp (y i))) ∧
    2 * (Real.exp (∑ i ∈ s, y i) -
      (1 - ∑ i ∈ s, (1 - Real.exp (y i)))) ≤
      (s.card : ℝ) * ((s.card : ℝ) - 1) := by
  classical
  have h := AvramDividend.Classical.avram_redux18_finite_mark_product_collision
    s (fun i => Real.exp (y i))
    (fun i => le_of_lt (Real.exp_pos (y i)))
    (fun i => Real.exp_le_one_iff.mpr (hy i))
  simpa only [Real.exp_sum] using h
