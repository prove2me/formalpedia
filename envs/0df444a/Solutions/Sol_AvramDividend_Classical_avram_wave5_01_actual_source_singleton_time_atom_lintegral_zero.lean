-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_source_singleton_time_atom_lintegral_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T08:59:20.581948+00:00
-- url     : https://prove2.me/submissions/28849d5d-028b-49b0-a28a-3d7b264974e9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_time_support_lebesgue_null_pathwise
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_measure_single_time_atom_exact

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (νt : Measure ℝ≥0) [NullSingletonClass νt]
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ t : ℝ≥0,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        ({t} ×ˢ B) ∂νt) = 0 := by
  let j : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let J : Set ℝ≥0 := {t | 0 < t ∧ j t ≠ 0}
  have hNull : νt J = 0 :=
    avram_wave5_01_actual_source_jump_time_support_lebesgue_null_pathwise
      X ω νt
  have hAe : ∀ᵐ t ∂νt, t ∉ J := by
    rw [ae_iff]
    simpa [J] using hNull
  have hZero : ∀ᵐ t ∂νt,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        ({t} ×ˢ B) = 0 := by
    filter_upwards [hAe] with t ht
    rw [avram_wave5_01_actual_source_jump_measure_single_time_atom_exact
      X ω t B hB]
    have hSet : {u : ℝ≥0 | u = t ∧ 0 < u ∧ j u ≠ 0 ∧ j u ∈ B} =
        ∅ := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hu
      have hut : u = t := hu.1
      subst u
      exact ht ⟨hu.2.1, hu.2.2.1⟩
    change (({u : ℝ≥0 | u = t ∧ 0 < u ∧ j u ≠ 0 ∧ j u ∈ B}).encard : ℝ≥0∞) = 0
    simp [hSet]
  exact (lintegral_congr_ae hZero).trans (by simp)
