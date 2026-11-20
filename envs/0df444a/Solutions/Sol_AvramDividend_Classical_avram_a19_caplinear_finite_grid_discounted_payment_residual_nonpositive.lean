-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_caplinear_finite_grid_discounted_payment_residual_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T23:50:53.73578+00:00
-- url     : https://prove2.me/submissions/f0e9bd8c-1055-4527-a571-4086ea4d0f5a

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-- Summing every original finite-cap right-dividend payment cell gives a nonpositive discounted residual. -/
theorem solution
    {ι : Type*} (s : Finset ι) (w : ℝ → ℝ) (C : ℝ)
    (Y D E : ι → ℝ)
    (hY : ∀ i ∈ s, Y i ≤ C)
    (hD : ∀ i ∈ s, 0 ≤ D i)
    (hE : ∀ i ∈ s, 0 ≤ E i)
    (hSlope : ∀ i ∈ s, ∀ z : ℝ,
      Y i ≤ z → z ≤ C → z - Y i ≤ w z - w (Y i)) :
    (∑ i ∈ s, E i * (D i + w (Y i) -
      (if Y i + D i ≤ C then w (Y i + D i)
       else w C + (Y i + D i - C)))) ≤ 0  := by
  apply Finset.sum_nonpos
  intro i hi
  have hCell : D i + w (Y i) -
      (if Y i + D i ≤ C then w (Y i + D i)
       else w C + (Y i + D i - C)) ≤ 0 := by
    by_cases hCap : Y i + D i ≤ C
    · simp only [if_pos hCap]
      have hSecant := hSlope i hi (Y i + D i)
        (by linarith [hD i hi]) hCap
      linarith
    · simp only [if_neg hCap]
      have hSecant := hSlope i hi C (hY i hi) le_rfl
      linarith
  exact mul_nonpos_of_nonneg_of_nonpos (hE i hi) hCell
