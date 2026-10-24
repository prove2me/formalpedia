-- Prove2me | solution 2 for AvramDividend.Classical.small_negative_jump_deficit_integral_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T13:13:55.492916+00:00
-- url     : https://prove2.me/submissions/048cae63-3eb9-4754-af2e-04f81d6ddd70

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Theorems.Thm_AvramDividend_Classical_small_negative_jump_deficit_integral_of_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Set

open AvramDividend.Classical

/-- The previously established integrable-jump theorem gives the required limit. -/
theorem solution
    (ν : Measure ℝ)
    (hint : IntegrableOn (fun y : ℝ => -y) (Ioo (-1 : ℝ) 0) ν)
    (hmeas : ∀ᶠ θ : ℝ in atTop,
      AEStronglyMeasurable
        (fun y : ℝ => (1 - Real.exp (θ * y)) / θ)
        (ν.restrict (Ioo (-1 : ℝ) 0)))
    (hsupport : ∀ᵐ y ∂(ν.restrict (Ioo (-1 : ℝ) 0)), y ≤ (0 : ℝ)) :
    Tendsto (fun θ : ℝ => ∫ y in Ioo (-1 : ℝ) 0,
      (1 - Real.exp (θ * y)) / θ ∂ν)
      atTop (nhds (0 : ℝ)) := by
  exact small_negative_jump_deficit_integral_of_integrable ν hint

