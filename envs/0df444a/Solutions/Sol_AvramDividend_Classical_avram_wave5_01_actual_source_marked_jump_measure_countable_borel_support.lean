-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_source_marked_jump_measure_countable_borel_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:47:47.793041+00:00
-- url     : https://prove2.me/submissions/1009dd77-d4bb-4ef2-8025-1a527e21007c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_all_original_levy_jump_times_countable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    ∃ S : Set (ℝ≥0 × ℝ),
      S.Countable ∧ MeasurableSet S ∧
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) Sᶜ = 0 := by
  classical
  let J : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let T : Set ℝ≥0 := {u | 0 < u ∧ J u ≠ 0}
  let g : ℝ≥0 → ℝ≥0 × ℝ := fun u => (u, J u)
  have hT : T.Countable := by
    simpa only [T, J, sub_ne_zero] using
      (avram_wave4_p2_all_original_levy_jump_times_countable X ω)
  have hJ : Measurable J := by
    exact (avram_wave4_04a_actual_levy_jumpmark_joint_measurable X).comp
      (measurable_id.prodMk measurable_const)
  have hg : Measurable g := measurable_id.prodMk hJ
  let S : Set (ℝ≥0 × ℝ) := g '' T
  have hS : S.Countable := hT.image g
  have hSm : MeasurableSet S := hS.measurableSet
  refine ⟨S, hS, hSm, ?_⟩
  have hEmpty : (g ⁻¹' Sᶜ) ∩ T = ∅ := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false]
    intro hu
    exact hu.1 ⟨u, hu.2, rfl⟩
  change ((Measure.count.restrict T).map g) Sᶜ = 0
  have hPre : MeasurableSet (g ⁻¹' Sᶜ) := hSm.compl.preimage hg
  rw [Measure.map_apply hg hSm.compl]
  rw [Measure.restrict_apply hPre]
  rw [hEmpty]
  simp
