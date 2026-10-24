-- Prove2me | solution 1 for AvramDividend.Classical.discounted_stieltjes_finite_measure_payout_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:01:25.095746+00:00
-- url     : https://prove2.me/submissions/447a2648-3d93-44de-b1a4-33251a70cbf5

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_integrableOn_of_finite_measure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- The extended-nonnegative Stieltjes payout agrees exactly with the
    embedded real integral on a finite-mass nonnegative payment window. -/
theorem solution
    (q : ℝ) (hq : 0 ≤ q) (μ : Measure ℝ) (A : Set ℝ)
    (hAmeas : MeasurableSet A)
    (hAnonneg : ∀ t ∈ A, 0 ≤ t)
    (hfinite : μ A ≠ ⊤) :
    (∫⁻ t in A, ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) =
      ENNReal.ofReal (∫ t in A, Real.exp (-(q * t)) ∂μ) := by
  have hInt :=
    AvramDividend.Classical.discounted_stieltjes_integrableOn_of_finite_measure
      q hq μ A hAmeas hAnonneg hfinite
  symm
  apply MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
  exact Filter.Eventually.of_forall (fun t : ℝ =>
    le_of_lt (Real.exp_pos (-(q * t))))
