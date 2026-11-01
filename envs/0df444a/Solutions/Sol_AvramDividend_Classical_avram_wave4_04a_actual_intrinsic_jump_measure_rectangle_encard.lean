-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:20:57.934993+00:00
-- url     : https://prove2.me/submissions/807cb926-ecac-4760-ae92-42e52283896b

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
    (ω : Ω) (s t : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) =
    ({u : ℝ≥0 | 0 < u ∧ s < u ∧ u ≤ t ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}).encard := by
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
  have hrect : MeasurableSet (Ioc s t ×ˢ B) := measurableSet_Ioc.prod hB
  have hpre : MeasurableSet ((fun u : ℝ≥0 => (u, j u)) ⁻¹' (Ioc s t ×ˢ B)) :=
    hrect.preimage hF
  change ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j u ≠ 0}).map
    (fun u => (u, j u))) (Ioc s t ×ˢ B) =
    ({u : ℝ≥0 | 0 < u ∧ s < u ∧ u ≤ t ∧ j u ≠ 0 ∧ j u ∈ B}).encard
  rw [Measure.map_apply hF hrect]
  rw [Measure.restrict_apply hpre]
  rw [Measure.count_apply (hpre.inter hS)]
  apply congrArg (fun T : Set ℝ≥0 => (T.encard : ℝ≥0∞))
  ext u
  simp [Set.mem_prod, Set.mem_preimage, Set.mem_inter_iff, j,
    and_assoc, and_left_comm, and_comm]
