-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_source_marked_jump_measure_arbitrary_borel_count_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:00:43.500276+00:00
-- url     : https://prove2.me/submissions/cfea8e82-350e-41dc-a39f-5e825ea17a4a

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
    (A : Set (ℝ≥0 × ℝ)) (hA : MeasurableSet A) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) A =
    ({u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ∈ A}).encard := by
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
  have hpre : MeasurableSet
      ((fun u : ℝ≥0 => (u, Δ u)) ⁻¹' A) :=
    hA.preimage hφ
  change ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ Δ u ≠ 0}).map
    (fun u => (u, Δ u))) A =
    ({u : ℝ≥0 | 0 < u ∧ Δ u ≠ 0 ∧ (u, Δ u) ∈ A}).encard
  rw [Measure.map_apply hφ hA]
  rw [Measure.restrict_apply hpre]
  rw [Measure.count_apply (hpre.inter hJ)]
  apply congrArg (fun T : Set ℝ≥0 => (T.encard : ℝ≥0∞))
  ext u
  simp [Set.mem_preimage, Set.mem_inter_iff, and_assoc,
    and_left_comm, and_comm]
