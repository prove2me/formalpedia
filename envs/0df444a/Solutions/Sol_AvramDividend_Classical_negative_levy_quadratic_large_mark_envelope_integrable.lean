-- Prove2me | solution 1 for AvramDividend.Classical.negative_levy_quadratic_large_mark_envelope_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T21:26:40.290497+00:00
-- url     : https://prove2.me/submissions/279bde75-7f01-44dd-b1c2-f98210beadd7

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution (ν : Measure ℝ)
    (hQuad : (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) < ⊤)
    (hLarge : IntegrableOn (fun y : ℝ => y) (Iic (-1 : ℝ)) ν)
    (θ : ℝ) :
    Integrable (fun y : ℝ =>
      θ / 2 * min 1 (y ^ 2) +
        |(Iic (-1 : ℝ)).indicator (fun z : ℝ => z) y|) ν := by
  have hMeas : AEStronglyMeasurable (fun y : ℝ => min 1 (y ^ 2)) ν :=
    (by fun_prop : Measurable (fun y : ℝ => min 1 (y ^ 2))).aestronglyMeasurable
  have hNonneg : 0 ≤ᵐ[ν] (fun y : ℝ => min 1 (y ^ 2)) :=
    Filter.Eventually.of_forall (fun y => by positivity)
  have hMin : Integrable (fun y : ℝ => min 1 (y ^ 2)) ν :=
    (lintegral_ofReal_ne_top_iff_integrable hMeas hNonneg).mp (ne_of_lt hQuad)
  have hInd : Integrable
      ((Iic (-1 : ℝ)).indicator (fun y : ℝ => y)) ν :=
    (integrable_indicator_iff measurableSet_Iic).2 hLarge
  exact (hMin.const_mul (θ / 2)).add hInd.abs
