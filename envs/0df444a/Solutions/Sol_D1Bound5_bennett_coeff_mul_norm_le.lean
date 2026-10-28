-- Prove2me | solution 1 for D1Bound5.bennett_coeff_mul_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:08:14.457133+00:00
-- url     : https://prove2.me/submissions/439fede6-6587-46ae-abef-1a8df84b25a4

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
open Finset

namespace D1Bound5





/-- Norm coefficient majorants multiply by the actual Cauchy product. -/
theorem _root_.solution
    (B C : PowerSeries ℂ) (D E : PowerSeries ℝ)
    (hB : ∀ h, ‖PowerSeries.coeff h B‖ ≤ PowerSeries.coeff h D)
    (hC : ∀ h, ‖PowerSeries.coeff h C‖ ≤ PowerSeries.coeff h E) (t : ℕ) :
    ‖PowerSeries.coeff t (B * C)‖ ≤ PowerSeries.coeff t (D * E) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  calc
    _ ≤ ∑ hu ∈ antidiagonal t,
      ‖PowerSeries.coeff hu.1 B * PowerSeries.coeff hu.2 C‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro hu hhu
      rw [norm_mul]
      exact mul_le_mul (hB hu.1) (hC hu.2) (norm_nonneg _)
        ((norm_nonneg _).trans (hB hu.1))











end D1Bound5
end
