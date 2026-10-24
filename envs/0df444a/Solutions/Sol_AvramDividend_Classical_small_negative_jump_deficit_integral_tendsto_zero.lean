-- Prove2me | solution 1 for AvramDividend.Classical.small_negative_jump_deficit_integral_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T13:13:55.093623+00:00
-- url     : https://prove2.me/submissions/2315c85e-ad0a-41c5-8834-817bf30ee2a5

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Theorems.Thm_AvramDividend_Classical_small_negative_jump_deficit_integral_of_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Set
open AvramDividend.Classical

/-- The established dominated-convergence theorem needs only first-moment
integrability; the extra measurable-support assumptions are automatic. -/
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
