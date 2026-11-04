-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:11:13.855884+00:00
-- url     : https://prove2.me/submissions/5b0552ad-fb38-4b0c-981c-5d9901a7b6d7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual intrinsic band count equals the cardinality of source marked jump times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) =
    ({u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard : ℝ≥0∞) := by
  let S : Set ℝ≥0 := {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -(1 / ((n : ℝ) + 1))}
  have hFinite : S.Finite :=
    avram_wave7_06_original_negative_band_marked_times_finite X ω T n
  have hSet : {u : ℝ≥0 | 0 < u ∧ 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ Iic (-(1 / ((n : ℝ) + 1)))} = S := by
    ext u
    constructor
    · rintro ⟨hu0, _, huT, _, hmark⟩
      exact ⟨hu0, huT, hmark⟩
    · rintro ⟨hu0, huT, hmark⟩
      refine ⟨hu0, hu0, huT, ?_, hmark⟩
      intro hzero
      have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      rw [hzero] at hmark
      linarith
  have hRect :=
    avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
      X ω 0 T (Iic (-(1 / ((n : ℝ) + 1)))) measurableSet_Iic
  rw [hSet] at hRect
  change _ = (S.ncard : ℝ≥0∞)
  rw [hRect, Set.ncard_eq_toFinset_card S hFinite]
  exact_mod_cast hFinite.encard_eq_coe_toFinset_card
