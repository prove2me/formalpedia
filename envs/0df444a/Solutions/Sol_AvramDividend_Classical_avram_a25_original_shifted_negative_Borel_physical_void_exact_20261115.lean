-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_original_shifted_negative_Borel_physical_void_exact_20261115
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T15:26:10.352696+00:00
-- url     : https://prove2.me/submissions/891d547c-b221-45f9-abe2-668a68279f35

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_intrinsic_marked_count_stationary_law
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_intrinsic_marked_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_a124_original_negative_Borel_physical_void_probability_exact_poisson_exponential_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Source Poisson void formula on every shifted negative-Borel physical cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (s T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    (P {ω | NX ω (Ioc s (s + T) ×ˢ B) = 0}).toReal =
      Real.exp (-((T : ℝ) * (X.ν B).toReal)) := by
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  have hShift :
      Measurable (fun ω : Ω => NX ω (Ioc s (s + T) ×ˢ B)) := by
    simpa only [NX] using
      (avram_p2_e_compensator_original_intrinsic_marked_count_measurable
        X s (s + T)
        (show s ≤ s + T from le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ T from zero_le))
        B hB)
  have hOrigin :
      Measurable (fun ω : Ω => NX ω (Ioc 0 T ×ˢ B)) := by
    simpa only [NX] using
      (avram_p2_e_compensator_original_intrinsic_marked_count_measurable
        X 0 T (show (0 : ℝ≥0) ≤ T from zero_le) B hB)
  have hLaw :
      Measure.map (fun ω : Ω => NX ω (Ioc s (s + T) ×ˢ B)) P =
      Measure.map (fun ω : Ω => NX ω (Ioc 0 T ×ˢ B)) P :=
    avram_p4_s3_interval_h_original_intrinsic_marked_count_stationary_law
      X NX (by intro ω; rfl) s T B hB
  have hSame :
      P {ω : Ω | NX ω (Ioc s (s + T) ×ˢ B) = 0} =
      P {ω : Ω | NX ω (Ioc 0 T ×ˢ B) = 0} := by
    change P ((fun ω => NX ω (Ioc s (s + T) ×ˢ B)) ⁻¹' {(0 : ℝ≥0∞)}) =
      P ((fun ω => NX ω (Ioc 0 T ×ˢ B)) ⁻¹' {(0 : ℝ≥0∞)})
    rw [← Measure.map_apply hShift (measurableSet_singleton 0),
      ← Measure.map_apply hOrigin (measurableSet_singleton 0), hLaw]
  change (P {ω : Ω | NX ω (Ioc s (s + T) ×ˢ B) = 0}).toReal =
    Real.exp (-((T : ℝ) * (X.ν B).toReal))
  rw [hSame]
  simpa only [NX] using
    (avram_a124_original_negative_Borel_physical_void_probability_exact_poisson_exponential_20261114
      X hFinite T B hB hNeg)
