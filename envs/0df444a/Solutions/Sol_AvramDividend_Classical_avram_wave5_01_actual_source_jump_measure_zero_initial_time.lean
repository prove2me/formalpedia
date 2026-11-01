-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_source_jump_measure_zero_initial_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T01:11:30.588273+00:00
-- url     : https://prove2.me/submissions/6840c1dd-259e-4b43-bd5f-d7e3c5d1e92a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (B : Set ℝ) (hB : MeasurableSet B) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      ({(0 : ℝ≥0)} ×ˢ B) = 0 := by
  let j : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  have hj : Measurable j := by
    exact (avram_wave4_04a_actual_levy_jumpmark_joint_measurable X).comp
      (Measurable.prodMk measurable_id measurable_const)
  have hpos : MeasurableSet {u : ℝ≥0 | 0 < u} :=
    measurableSet_lt measurable_const measurable_id
  have hnonzero : MeasurableSet {u : ℝ≥0 | j u ≠ 0} :=
    (measurableSet_eq_fun hj measurable_const).compl
  have hS : MeasurableSet {u : ℝ≥0 | 0 < u ∧ j u ≠ 0} :=
    hpos.inter hnonzero
  have hF : Measurable (fun u : ℝ≥0 => (u, j u)) :=
    Measurable.prodMk measurable_id hj
  have hrect : MeasurableSet ({(0 : ℝ≥0)} ×ˢ B) :=
    (measurableSet_singleton (0 : ℝ≥0)).prod hB
  have hpre : MeasurableSet ((fun u : ℝ≥0 => (u, j u)) ⁻¹'
      ({(0 : ℝ≥0)} ×ˢ B)) := hrect.preimage hF
  change ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j u ≠ 0}).map
    (fun u : ℝ≥0 => (u, j u))) ({(0 : ℝ≥0)} ×ˢ B) = 0
  rw [Measure.map_apply hF hrect]
  rw [Measure.restrict_apply hpre]
  rw [Measure.count_apply (hpre.inter hS)]
  have hempty : ((fun u : ℝ≥0 => (u, j u)) ⁻¹'
      ({(0 : ℝ≥0)} ×ˢ B)) ∩ {u : ℝ≥0 | 0 < u ∧ j u ≠ 0} = ∅ := by
    ext u
    constructor
    · intro hu
      rcases hu with ⟨⟨hu0, _⟩, ⟨huPos, _⟩⟩
      have hz : u = 0 := Set.mem_singleton_iff.mp hu0
      exact False.elim ((lt_irrefl (0 : ℝ≥0)) (hz ▸ huPos))
    · simp
  rw [hempty]
  simp
