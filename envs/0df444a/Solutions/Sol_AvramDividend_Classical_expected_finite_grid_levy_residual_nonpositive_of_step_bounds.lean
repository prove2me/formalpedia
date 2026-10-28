-- Prove2me | solution 1 for AvramDividend.Classical.expected_finite_grid_levy_residual_nonpositive_of_step_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:21:03.048961+00:00
-- url     : https://prove2.me/submissions/fbd0e12b-09ec-48e5-b6a1-10ad77f8a0f5

import Mathlib.Data.Finset.Range
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Finset
open AvramDividend.Classical

/-- Sum the nonpositive expected Lévy generator residuals over a finite
verification grid using Bochner-integral linearity. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (r : ℕ → Ω → ℝ)
    (hInt : ∀ k, Integrable (r k) P)
    (hStep : ∀ k, (∫ ω, r k ω ∂P) ≤ 0)
    (n : ℕ) :
    (∫ ω, ∑ k ∈ Finset.range n, r k ω ∂P) ≤ 0 := by
  have hsum (m : ℕ) :
      Integrable (fun ω => ∑ k ∈ Finset.range m, r k ω) P := by
    apply integrable_finset_sum
    intro k hk
    exact hInt k
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit :
        (∫ ω, ∑ k ∈ Finset.range (n + 1), r k ω ∂P) =
          (∫ ω, ∑ k ∈ Finset.range n, r k ω ∂P) +
            (∫ ω, r n ω ∂P) := by
      simp only [Finset.sum_range_succ]
      exact integral_add (hsum n) (hInt n)
    rw [hsplit]
    exact add_nonpos ih (hStep n)
