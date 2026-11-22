-- Prove2me | solution 2 for AvramDividend.Classical.negative_levy_tail_real_integral_bridge
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T07:57:09.764697+00:00
-- url     : https://prove2.me/submissions/a5a452bc-356d-4c31-863b-721112494550
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_negative_levy_compensated_primitive_integrable
import Theorems.Thm_AvramDividend_Classical_negative_levy_tail_finite_of_quadratic
import Theorems.Thm_AvramDividend_Classical_negative_levy_real_tail_tonelli_of_integrable
import Mathlib
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal


theorem solution
    (ν : Measure ℝ) (hSupp : ν (Ici (0 : ℝ)) = 0)
    (hQuad : (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) < ⊤)
    (hLarge : IntegrableOn (fun y : ℝ => y) (Iic (-1 : ℝ)) ν)
    (θ : ℝ) (hθ : 0 < θ) :
    Integrable (fun y : ℝ => ∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t)) ν ∧
    IntegrableOn (fun t : ℝ => (1 - Real.exp (-θ * t)) * (ν (Iio (-t))).toReal) (Ioi (0 : ℝ)) ∧
    (∫ y : ℝ, ∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t) ∂ν) =
    (∫ t in Ioi (0 : ℝ),
      (1 - Real.exp (-θ * t)) * (ν (Iio (-t))).toReal) := by
  have hFn := negative_levy_compensated_primitive_integrable
    ν hSupp hQuad hLarge θ hθ
  have hTail := negative_levy_tail_finite_of_quadratic ν hQuad
  have hReal := negative_levy_real_tail_tonelli_of_integrable
    ν hSupp hTail θ hθ hFn
  exact ⟨hFn, hReal.1, hReal.2⟩
