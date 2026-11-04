-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_original_finite_nu_past_real_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:41:31.130586+00:00
-- url     : https://prove2.me/submissions/ac080877-55e1-4c9c-b8ff-4aee140dcffc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_intrinsic_future_rectangle_past_factor_of_measurable_extractor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- On every original past-filtration event, finite-rate source marked count
has real set-integral equal to the original Levy intensity times event mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hν : X.ν B < ⊤)
    (hRate : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) :
    (∫ ω in A, (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal ∂P) =
      (P A * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal := by
  haveI : IsProbabilityMeasure P := X.isProbability
  let N : Ω → ℝ≥0∞ := fun ω => ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
  have hNmeas : Measurable N :=
    avram_p2_e_compensator_intrinsic_rectangle_count_measurable
      X s t hst B hB
  obtain ⟨F, hF, hExtract⟩ :=
    avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
      X s t hst B hB
  have hRect :=
    avram_wave7_01_intrinsic_future_rectangle_past_factor_of_measurable_extractor
      X s t hst A hA B hB F hF hExtract
  have hMean : (∫⁻ ω in A, N ω ∂P) =
      P A * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by
    rw [hRect, hRate]
  have hFinite : (∫⁻ ω in A, N ω ∂P) ≠ ⊤ := by
    rw [hMean]
    exact ne_of_lt (ENNReal.mul_lt_top (measure_lt_top P A)
      (ENNReal.mul_lt_top ENNReal.coe_lt_top hν))
  calc
    (∫ ω in A, (N ω).toReal ∂P) =
        (∫⁻ ω in A, N ω ∂P).toReal :=
      integral_toReal hNmeas.aemeasurable (ae_lt_top hNmeas hFinite)
    _ = (P A * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal :=
      congrArg ENNReal.toReal hMean
