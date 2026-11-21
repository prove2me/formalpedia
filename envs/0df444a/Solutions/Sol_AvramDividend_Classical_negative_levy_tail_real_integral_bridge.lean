-- Prove2me | solution 1 for AvramDividend.Classical.negative_levy_tail_real_integral_bridge
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T21:22:24.751505+00:00
-- url     : https://prove2.me/submissions/fbb0a088-8f77-49a5-8a39-c13a4d30c18d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_negative_levy_compensated_primitive_integrable
import Theorems.Thm_AvramDividend_Classical_negative_levy_tail_finite_of_quadratic
import Theorems.Thm_AvramDividend_Classical_negative_levy_real_tail_tonelli_of_integrable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (ν : Measure ℝ) (hSupp : ν (Ici (0 : ℝ)) = 0)
    (hQuad : (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) < ⊤)
    (hLarge : IntegrableOn (fun y : ℝ => y) (Iic (-1 : ℝ)) ν)
    (θ : ℝ) (hθ : 0 < θ) :
    Integrable (fun y : ℝ => ∫ t in (0 : ℝ)..(-y),
      1 - Real.exp (-θ * t)) ν ∧
    IntegrableOn (fun t : ℝ => (1 - Real.exp (-θ * t)) *
      (ν (Iio (-t))).toReal) (Ioi (0 : ℝ)) ∧
    (∫ y : ℝ, ∫ t in (0 : ℝ)..(-y),
      1 - Real.exp (-θ * t) ∂ν) =
    (∫ t in Ioi (0 : ℝ),
      (1 - Real.exp (-θ * t)) * (ν (Iio (-t))).toReal) := by
  have hF := negative_levy_compensated_primitive_integrable
    ν hSupp hQuad hLarge θ hθ
  have hTail := negative_levy_tail_finite_of_quadratic ν hQuad
  have hTon := negative_levy_real_tail_tonelli_of_integrable
    ν hSupp hTail θ hθ hF
  exact ⟨hF, hTon⟩
