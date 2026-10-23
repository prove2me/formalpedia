-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_weighted_square_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T11:50:51.866856+00:00
-- url     : https://prove2.me/submissions/381543d4-0a93-4bfb-8c12-0f902f8b8a56

import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_damped_quadratic_integrable
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

/-- Reuse the already-proved, definitionally identical Esscher square integrability. -/
theorem solution
    (μ : Measure ℝ) (φ : ℝ) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(φ * z)) * z ^ 2) ∂μ) < ⊤ := by
  exact gaussian_esscher_damped_quadratic_integrable μ φ hφ hlevy
