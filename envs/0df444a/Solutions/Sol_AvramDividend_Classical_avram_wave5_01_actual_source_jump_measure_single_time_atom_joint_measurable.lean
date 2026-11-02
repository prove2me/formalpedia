-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_source_jump_measure_single_time_atom_joint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T08:59:24.715375+00:00
-- url     : https://prove2.me/submissions/a9b94659-3706-4649-89b5-75f7c8f7414f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
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
    (B : Set ℝ) (hB : MeasurableSet B) :
    Measurable (fun z : ℝ≥0 × Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u z.2 - Function.leftLim
          (fun v : ℝ≥0 => X.X v z.2) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u z.2 - Function.leftLim
            (fun v : ℝ≥0 => X.X v z.2) u)))
        ({z.1} ×ˢ B)) := by
  classical
  let Δ : ℝ≥0 × Ω → ℝ := fun z =>
    X.X z.1 z.2 - Function.leftLim (fun v : ℝ≥0 => X.X v z.2) z.1
  have hΔ : Measurable Δ :=
    avram_wave4_04a_actual_levy_jumpmark_joint_measurable X
  have hPositive : MeasurableSet {z : ℝ≥0 × Ω | 0 < z.1} :=
    measurableSet_lt measurable_const measurable_fst
  have hNonzero : MeasurableSet {z : ℝ≥0 × Ω | Δ z ≠ 0} :=
    (measurableSet_eq_fun hΔ measurable_const).compl
  have hIn : MeasurableSet {z : ℝ≥0 × Ω | Δ z ∈ B} :=
    hB.preimage hΔ
  have hEvent : MeasurableSet
      {z : ℝ≥0 × Ω | 0 < z.1 ∧ Δ z ≠ 0 ∧ Δ z ∈ B} :=
    hPositive.inter (hNonzero.inter hIn)
  have hEq : (fun z : ℝ≥0 × Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u z.2 - Function.leftLim
          (fun v : ℝ≥0 => X.X v z.2) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u z.2 - Function.leftLim
            (fun v : ℝ≥0 => X.X v z.2) u)))
        ({z.1} ×ˢ B)) =
      (fun z => if 0 < z.1 ∧ Δ z ≠ 0 ∧ Δ z ∈ B
        then (1 : ℝ≥0∞) else 0) := by
    funext z
    classical
    rw [avram_wave5_01_actual_source_jump_measure_single_time_atom_exact
      X z.2 z.1 B hB]
    let j : ℝ≥0 → ℝ := fun u =>
      X.X u z.2 - Function.leftLim (fun v : ℝ≥0 => X.X v z.2) u
    change (({u : ℝ≥0 | u = z.1 ∧ 0 < u ∧ j u ≠ 0 ∧ j u ∈ B}).encard : ℝ≥0∞) =
      if 0 < z.1 ∧ j z.1 ≠ 0 ∧ j z.1 ∈ B then 1 else 0
    by_cases h : 0 < z.1 ∧ j z.1 ≠ 0 ∧ j z.1 ∈ B
    · have hSet : {u : ℝ≥0 | u = z.1 ∧ 0 < u ∧ j u ≠ 0 ∧ j u ∈ B} =
          {z.1} := by
        ext u
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        exact ⟨fun hu => hu.1, fun hu => by subst u; exact ⟨rfl, h.1, h.2.1, h.2.2⟩⟩
      simp [hSet, h]
    · have hSet : {u : ℝ≥0 | u = z.1 ∧ 0 < u ∧ j u ≠ 0 ∧ j u ∈ B} =
          ∅ := by
        ext u
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro hu
        have hut : u = z.1 := hu.1
        subst u
        exact h ⟨hu.2.1, hu.2.2.1, hu.2.2.2⟩
      simp [hSet, h]
  rw [hEq]
  exact measurable_const.ite hEvent measurable_const
