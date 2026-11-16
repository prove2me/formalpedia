-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_original_shifted_negative_Borel_twojump_collision_bound_20261115
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T15:12:39.564529+00:00
-- url     : https://prove2.me/submissions/fc4a7c84-dcc2-46f4-a7d8-f90d3bdc376d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_intrinsic_marked_count_stationary_law
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_intrinsic_marked_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_a25_original_negative_Borel_physical_twojump_collision_bound_20261115
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Stationarity transports quadratic source collisions to all grid cells. -/
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
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    (P {ω | (2 : ℝ) ≤ (NX ω (Ioc s (s + T) ×ˢ B)).toReal}).toReal ≤
      r ^ 2 / 2 := by
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let A : Set ℝ≥0∞ := {z | (2 : ℝ) ≤ z.toReal}
  have hA : MeasurableSet A := by
    change MeasurableSet (ENNReal.toReal ⁻¹' Ici (2 : ℝ))
    exact ENNReal.measurable_toReal measurableSet_Ici
  have hShift :
      Measurable (fun ω : Ω => NX ω (Ioc s (s + T) ×ˢ B)) := by
    simpa only [NX] using
      (avram_p2_e_compensator_original_intrinsic_marked_count_measurable
        X s (s + T) (show s ≤ s + T from le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ T from zero_le)) B hB)
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
      (P {ω | (2 : ℝ) ≤ (NX ω (Ioc s (s + T) ×ˢ B)).toReal}).toReal =
      (P {ω | (2 : ℝ) ≤ (NX ω (Ioc 0 T ×ˢ B)).toReal}).toReal := by
    change (P ((fun ω => NX ω (Ioc s (s + T) ×ˢ B)) ⁻¹' A)).toReal =
      (P ((fun ω => NX ω (Ioc 0 T ×ˢ B)) ⁻¹' A)).toReal
    rw [← Measure.map_apply hShift hA, ← Measure.map_apply hOrigin hA, hLaw]
  have hBound := avram_a25_original_negative_Borel_physical_twojump_collision_bound_20261115
    X hFinite T B hB hNeg
  have hBound' :
      (P {ω | (2 : ℝ) ≤ (NX ω (Ioc 0 T ×ˢ B)).toReal}).toReal ≤
        (((T : ℝ≥0∞) * X.ν B).toReal) ^ 2 / 2 := by
    simpa only [NX] using hBound
  exact hSame.le.trans hBound'
