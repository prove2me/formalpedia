-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_source_jump_measure_single_time_atom_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T08:52:38.000458+00:00
-- url     : https://prove2.me/submissions/86e9e4a7-a405-4f26-aa84-6e353c1c8baf

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
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (t : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      ({t} ×ˢ B) =
    ({u : ℝ≥0 | u = t ∧ 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}).encard := by
  let Δ : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  have hΔ : Measurable Δ := by
    exact (avram_wave4_04a_actual_levy_jumpmark_joint_measurable X).comp
      (Measurable.prodMk measurable_id measurable_const)
  have hPos : MeasurableSet {u : ℝ≥0 | 0 < u} :=
    measurableSet_lt measurable_const measurable_id
  have hNonzero : MeasurableSet {u : ℝ≥0 | Δ u ≠ 0} :=
    (measurableSet_eq_fun hΔ measurable_const).compl
  have hJ : MeasurableSet {u : ℝ≥0 | 0 < u ∧ Δ u ≠ 0} :=
    hPos.inter hNonzero
  have hφ : Measurable (fun u : ℝ≥0 => (u, Δ u)) :=
    Measurable.prodMk measurable_id hΔ
  have hC : MeasurableSet ({t} ×ˢ B) :=
    (measurableSet_singleton t).prod hB
  have hpre : MeasurableSet
      ((fun u : ℝ≥0 => (u, Δ u)) ⁻¹' ({t} ×ˢ B)) :=
    hC.preimage hφ
  change ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ Δ u ≠ 0}).map
    (fun u => (u, Δ u))) ({t} ×ˢ B) =
    ({u : ℝ≥0 | u = t ∧ 0 < u ∧ Δ u ≠ 0 ∧ Δ u ∈ B}).encard
  rw [Measure.map_apply hφ hC]
  rw [Measure.restrict_apply hpre]
  rw [Measure.count_apply (hpre.inter hJ)]
  apply congrArg (fun T : Set ℝ≥0 => (T.encard : ℝ≥0∞))
  ext u
  simp [Set.mem_prod, Set.mem_preimage, Set.mem_inter_iff, and_assoc,
    and_left_comm, and_comm]
