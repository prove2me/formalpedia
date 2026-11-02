-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_original_marked_jump_count_finite_on_separated_band_every_path
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:00:19.108821+00:00
-- url     : https://prove2.me/submissions/bd1dd43d-de4a-44d3-8beb-00f05bba6225

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_marked_jump_measure_arbitrary_borel_count_exact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual intrinsic marked source measure is locally finite on every
mark band separated from zero, without a bounded-variation assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ {y : ℝ | δ ≤ dist y 0}) < ⊤ := by
  let m : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let B : Set ℝ := {y | δ ≤ dist y 0}
  have hB : MeasurableSet B := by
    exact (isClosed_le continuous_const
      (continuous_id.dist continuous_const)).measurableSet
  have hA : MeasurableSet (Ioc (0 : ℝ≥0) T ×ˢ B) :=
    measurableSet_Ioc.prod hB
  have hcount :=
    avram_wave5_01_actual_source_marked_jump_measure_arbitrary_borel_count_exact
      X ω (Ioc (0 : ℝ≥0) T ×ˢ B) hA
  have hfinite :
      {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧ δ ≤ dist (m u) 0}.Finite :=
    avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path
      X ω T δ hδ
  have hsub :
      {u : ℝ≥0 | 0 < u ∧ m u ≠ 0 ∧ (u, m u) ∈ Ioc 0 T ×ˢ B} ⊆
        {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧ δ ≤ dist (m u) 0} := by
    intro u hu
    exact ⟨hu.1, hu.2.2.1.2, hu.2.2.2⟩
  have hfinite' := hfinite.subset hsub
  change ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ m u ≠ 0}).map
    (fun u : ℝ≥0 => (u, m u))) (Ioc 0 T ×ˢ B) < ⊤
  rw [hcount]
  exact_mod_cast hfinite'.encard_lt_top
