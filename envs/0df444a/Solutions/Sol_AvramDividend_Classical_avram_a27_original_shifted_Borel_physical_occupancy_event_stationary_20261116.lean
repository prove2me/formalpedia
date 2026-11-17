-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_shifted_Borel_physical_occupancy_event_stationary_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T09:26:51.020919+00:00
-- url     : https://prove2.me/submissions/37f0dcc3-528d-4595-85b0-a8100408506d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_intrinsic_marked_count_stationary_law
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    P {ω : Ω | NX ω (Ioc s (s + T) ×ˢ B) ≠ 0} =
      P {ω : Ω | NX ω (Ioc 0 T ×ˢ B) ≠ 0} := by
  classical
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  change P {ω : Ω | NX ω (Ioc s (s + T) ×ˢ B) ≠ 0} =
    P {ω : Ω | NX ω (Ioc 0 T ×ˢ B) ≠ 0}
  have hLaw :=
    avram_p4_s3_interval_h_original_intrinsic_marked_count_stationary_law
      X NX (by intro ω; rfl) s T B hB
  have hm : Measurable (fun ω : Ω => NX ω (Ioc s (s + T) ×ˢ B)) := by
    simpa only [NX] using
      (avram_p2_e_compensator_intrinsic_rectangle_count_measurable
        X s (s + T) (le_add_of_nonneg_right bot_le) B hB)
  have hm0 : Measurable (fun ω : Ω => NX ω (Ioc 0 T ×ˢ B)) := by
    simpa only [NX] using
      (avram_p2_e_compensator_intrinsic_rectangle_count_measurable
        X 0 T bot_le B hB)
  have hset : MeasurableSet {x : ℝ≥0∞ | x ≠ 0} := by
    exact (measurableSet_singleton 0).compl
  have hl : P {ω : Ω | NX ω (Ioc s (s + T) ×ˢ B) ≠ 0} =
      (P.map (fun ω : Ω => NX ω (Ioc s (s + T) ×ˢ B))) {x : ℝ≥0∞ | x ≠ 0} := by
    rw [Measure.map_apply hm hset] <;> rfl
  have hr : P {ω : Ω | NX ω (Ioc 0 T ×ˢ B) ≠ 0} =
      (P.map (fun ω : Ω => NX ω (Ioc 0 T ×ˢ B))) {x : ℝ≥0∞ | x ≠ 0} := by
    rw [Measure.map_apply hm0 hset] <;> rfl
  rw [hl, hr, hLaw]
