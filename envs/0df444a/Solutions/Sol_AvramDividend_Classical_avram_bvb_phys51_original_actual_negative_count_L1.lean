-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys51_original_actual_negative_count_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T15:06:55.406358+00:00
-- url     : https://prove2.me/submissions/78d8dbd4-f57d-48ea-aa09-0ee25094600e

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_intrinsic_marked_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_finite_activity_all_start_actual_negative_predictable_rectangle

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Under finite Lévy intensity, the actual original-process count of negative
jumps in a bounded deterministic interval has finite first moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    Integrable (fun ω : Ω =>
      (((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
        (Ioc (0 : ℝ≥0) T ×ˢ Iio (0 : ℝ))).toReal) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {t : ℝ≥0 |
      0 < t ∧ X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
      (fun t : ℝ≥0 => (t, X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
      (Ioc (0 : ℝ≥0) T ×ˢ Iio (0 : ℝ))
  have hm : Measurable N := by
    exact avram_p2_e_compensator_original_intrinsic_marked_count_measurable
      X 0 T (show (0 : ℝ≥0) ≤ T from bot_le) (Iio (0 : ℝ)) measurableSet_Iio
  have hrate := avram_wave7_01_bv_finite_activity_all_start_actual_negative_predictable_rectangle
    X hBV hFinite 0 T (show (0 : ℝ≥0) ≤ T from bot_le) Set.univ
    (by exact MeasurableSet.univ)
  have hlim : (∫⁻ ω, N ω ∂P) = (T : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
    simpa [N, MeasureTheory.setLIntegral_univ] using hrate
  have hfiniteT : (T : ℝ≥0∞) < ⊤ := ENNReal.coe_lt_top
  have hfiniteIntegral : (∫⁻ ω, N ω ∂P) < ⊤ := by
    rw [hlim]
    exact ENNReal.mul_lt_top hfiniteT hFinite
  change Integrable (fun ω => (N ω).toReal) P
  exact integrable_toReal_of_lintegral_ne_top hm.aemeasurable
    (ne_of_lt hfiniteIntegral)
