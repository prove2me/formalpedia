-- Prove2me | solution 1 for AvramDividend.Classical.negative_levy_real_tail_tonelli_outer_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T07:56:05.107238+00:00
-- url     : https://prove2.me/submissions/8e5b1759-deb9-49b5-829d-cbfffd3778f5

import Mathlib
import Theorems.Thm_AvramDividend_Classical_original_negative_levy_tail_tonelli
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_primitive_bounds
import Theorems.Thm_AvramDividend_Classical_negative_levy_tail_real_conversion_of_finite_lintegral
import Theorems.Thm_AvramDividend_Classical_integral_eq_toReal_lintegral_ofReal_nonneg
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution (ν : Measure ℝ) (hSupp : ν (Ici (0 : ℝ)) = 0)
    (hTailFin : ∀ t : ℝ, 0 < t → ν (Iio (-t)) < ⊤)
    (θ : ℝ) (hθ : 0 < θ)
    (hFn : Integrable (fun y : ℝ =>
      ∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t)) ν) :
    IntegrableOn (fun t : ℝ =>
      (1 - Real.exp (-θ * t)) * (ν (Iio (-t))).toReal)
      (Ioi (0 : ℝ)) ∧
    (∫ y : ℝ, (∫ t in (0 : ℝ)..(-y),
      1 - Real.exp (-θ * t)) ∂ν) =
    (∫ t in Ioi (0 : ℝ),
      (1 - Real.exp (-θ * t)) * (ν (Iio (-t))).toReal) := by
  have hAE : ∀ᵐ y ∂ν,
      0 ≤ (∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t)) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hSupp] with y hy
    have hy0 : y < 0 := lt_of_not_ge (by simpa only [mem_Ici] using hy)
    exact (levy_compensated_exponential_primitive_bounds
      θ (-y) hθ.le (by linarith)).1
  have hFin : (∫⁻ y : ℝ, ENNReal.ofReal
      (∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t)) ∂ν) ≠ ⊤ :=
    (lintegral_ofReal_ne_top_iff_integrable
      hFn.aestronglyMeasurable hAE).2 hFn
  have hTon := (original_negative_levy_tail_tonelli ν hSupp θ hθ).symm
  have hTail := negative_levy_tail_real_conversion_of_finite_lintegral
    ν hTailFin θ hθ
    (∫⁻ y : ℝ, ENNReal.ofReal
      (∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t)) ∂ν)
    hFin hTon
  have hReal := integral_eq_toReal_lintegral_ofReal_nonneg ν
    (fun y : ℝ => ∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t))
    hFn hAE
  refine ⟨hTail.1, ?_⟩
  calc
    (∫ y : ℝ, (∫ t in (0 : ℝ)..(-y),
      1 - Real.exp (-θ * t)) ∂ν) =
      (∫⁻ y : ℝ, ENNReal.ofReal
        (∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t)) ∂ν).toReal := hReal
    _ = (∫ t in Ioi (0 : ℝ),
      (1 - Real.exp (-θ * t)) * (ν (Iio (-t))).toReal) := hTail.2.symm
