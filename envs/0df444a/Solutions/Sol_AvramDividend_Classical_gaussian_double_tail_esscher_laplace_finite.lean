-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_esscher_laplace_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T07:32:35.662992+00:00
-- url     : https://prove2.me/submissions/649b9054-bc5a-4e76-b683-e29963b2c69c

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_esscher_laplace_transform
import Theorems.Thm_AvramDividend_Classical_gaussian_shifted_compensator_integrable
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical

/-- The weighted Gaussian double-tail Laplace transform is finite under the Lévy condition. -/
theorem solution
    (μ : Measure ℝ) [SFinite μ] (φ θ : ℝ)
    (hφ : 0 < φ) (hθ : 0 ≤ θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    ENNReal.ofReal (θ ^ 2) *
      (∫⁻ t : ℝ, ∫⁻ z : ℝ,
        (if 0 < t ∧ t < z then
          ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
            ENNReal.ofReal (Real.exp (-φ * z))
         else 0) ∂μ ∂volume) < ⊤ := by
  rw [gaussian_double_tail_esscher_laplace_transform μ φ θ hφ hθ]
  exact gaussian_shifted_compensator_integrable μ φ θ hφ hθ hlevy
