-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_source_single_time_jump_count_rightCont_filtration_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:00:35.585213+00:00
-- url     : https://prove2.me/submissions/3410ff82-1ac9-41fc-a98b-e9cbff6fb10c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_prejump_predictable_jumpmark_adapted
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_measure_single_time_atom_exact

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    Measurable[𝓕.rightCont t] (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u)))
        ({t} ×ˢ B)) := by
  classical
  let j : Ω → ℝ := fun ω =>
    X.X t ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) t
  have hj : Measurable[𝓕.rightCont t] j :=
    ((avram_wave4_04a_actual_levy_prejump_predictable_jumpmark_adapted X).2 t).measurable
  have hNonzero : MeasurableSet[𝓕.rightCont t] {ω : Ω | j ω ≠ 0} :=
    (measurableSet_eq_fun hj measurable_const).compl
  have hMark : MeasurableSet[𝓕.rightCont t] {ω : Ω | j ω ∈ B} :=
    hB.preimage hj
  have hE : MeasurableSet[𝓕.rightCont t]
      {ω : Ω | 0 < t ∧ j ω ≠ 0 ∧ j ω ∈ B} := by
    by_cases ht : 0 < t
    · simpa [ht, Set.setOf_and] using hNonzero.inter hMark
    · simpa [ht] using
        (MeasurableSet.empty : MeasurableSet[𝓕.rightCont t] (∅ : Set Ω))
  have hEq : (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u)))
        ({t} ×ˢ B)) =
      (fun ω => if 0 < t ∧ j ω ≠ 0 ∧ j ω ∈ B
        then (1 : ℝ≥0∞) else 0) := by
    funext ω
    classical
    rw [avram_wave5_01_actual_source_jump_measure_single_time_atom_exact
      X ω t B hB]
    let q : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    change (({u : ℝ≥0 | u = t ∧ 0 < u ∧ q u ≠ 0 ∧ q u ∈ B}).encard : ℝ≥0∞) =
      if 0 < t ∧ q t ≠ 0 ∧ q t ∈ B then 1 else 0
    by_cases h : 0 < t ∧ q t ≠ 0 ∧ q t ∈ B
    · have hSet : {u : ℝ≥0 | u = t ∧ 0 < u ∧ q u ≠ 0 ∧ q u ∈ B} =
          {t} := by
        ext u
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        exact ⟨fun hu => hu.1, fun hu => by subst u; exact ⟨rfl, h.1, h.2.1, h.2.2⟩⟩
      simp [hSet, h]
    · have hSet : {u : ℝ≥0 | u = t ∧ 0 < u ∧ q u ≠ 0 ∧ q u ∈ B} =
          ∅ := by
        ext u
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro hu
        have hut : u = t := hu.1
        subst u
        exact h ⟨hu.2.1, hu.2.2.1, hu.2.2.2⟩
      simp [hSet, h]
  rw [hEq]
  exact measurable_const.ite hE measurable_const
