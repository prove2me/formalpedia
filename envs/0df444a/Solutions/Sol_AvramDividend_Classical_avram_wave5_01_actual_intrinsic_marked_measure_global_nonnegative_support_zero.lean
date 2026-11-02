-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_intrinsic_marked_measure_global_nonnegative_support_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:10:24.242874+00:00
-- url     : https://prove2.me/submissions/b4e7df07-5f65-49b2-af57-b5c1b7fc26a2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_marked_jump_measure_arbitrary_borel_count_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Set.univ ×ˢ Ici (0 : ℝ)) = 0 := by
  classical
  let Δ : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  have hA : MeasurableSet ((Set.univ : Set ℝ≥0) ×ˢ Ici (0 : ℝ)) :=
    MeasurableSet.univ.prod measurableSet_Ici
  have hCount :=
    avram_wave5_01_actual_source_marked_jump_measure_arbitrary_borel_count_exact
      X ω (Set.univ ×ˢ Ici (0 : ℝ)) hA
  change ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ Δ u ≠ 0}).map
    (fun u => (u, Δ u))) (Set.univ ×ˢ Ici (0 : ℝ)) = 0
  rw [hCount]
  have hEmpty :
      {u : ℝ≥0 | 0 < u ∧ Δ u ≠ 0 ∧
        (u, Δ u) ∈ Set.univ ×ˢ Ici (0 : ℝ)} = ∅ := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hu
    have hle : Δ u ≤ 0 :=
      avram_wave4_04a_actual_levy_jumpmark_nonpositive X ω u hu.1
    have hge : 0 ≤ Δ u := hu.2.2.2
    exact hu.2.1 (le_antisymm hle hge)
  rw [hEmpty]
  simp
