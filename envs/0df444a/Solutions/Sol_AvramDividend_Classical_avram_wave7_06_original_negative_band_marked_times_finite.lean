-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_negative_band_marked_times_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T06:53:35.520108+00:00
-- url     : https://prove2.me/submissions/8739e3ab-2e3a-4999-bc3c-21099532cc07

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Finiteness of original marked source jump times, directly from càdlàg path compactness. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.Finite := by
  have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  apply (avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path
    X ω T (1 / ((n : ℝ) + 1)) hε).subset
  rintro u ⟨hu0, huT, hmark⟩
  refine ⟨hu0, huT, ?_⟩
  have hnonpos :
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ 0 := by
    linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonpos hnonpos]
  linarith
