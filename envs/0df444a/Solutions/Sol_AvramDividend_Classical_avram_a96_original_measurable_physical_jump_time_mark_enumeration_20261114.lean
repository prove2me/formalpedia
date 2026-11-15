-- Prove2me | solution 1 for AvramDividend.Classical.avram_a96_original_measurable_physical_jump_time_mark_enumeration_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:36:38.776814+00:00
-- url     : https://prove2.me/submissions/db5a9856-8766-4cf0-aaee-40a8f88c4c38

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_original_measurable_jump_enumeration
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ (T : ℕ → Ω → ℝ≥0) (A : ℕ → Set Ω)
      (Y : ℕ → Ω → ℝ),
      (∀ n, Measurable (T n)) ∧
      (∀ n, MeasurableSet (A n)) ∧
      (∀ n, Measurable (Y n)) ∧
      (∀ ω n, ω ∈ A n →
        0 < T n ω ∧
        Y n ω = X.X (T n ω) ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) (T n ω) ∧
        Y n ω ≠ 0) ∧
      (∀ ω n m, ω ∈ A n → ω ∈ A m →
        T n ω = T m ω → n = m) ∧
      (∀ ω u, 0 < u →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 →
        ∃ n, ω ∈ A n ∧ T n ω = u ∧
          Y n ω =
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) := by
  obtain ⟨T, A, hT, hA, hActive, hUnique, hCover⟩ :=
    avram_wave5_02a_actual_original_measurable_jump_enumeration X
  let Y : ℕ → Ω → ℝ := fun n ω =>
    X.X (T n ω) ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) (T n ω)
  have hJoint :=
    avram_wave4_04a_actual_levy_jumpmark_joint_measurable X
  have hYm (n : ℕ) : Measurable (Y n) := by
    exact hJoint.comp ((hT n).prodMk measurable_id)
  refine ⟨T, A, Y, hT, hA, hYm, ?_, hUnique, ?_⟩
  · intro ω n han
    obtain ⟨hpos, hnonzero⟩ := hActive ω n han
    exact ⟨hpos, rfl, hnonzero⟩
  · intro ω u hu hnonzero
    obtain ⟨n, han, huEq⟩ := hCover ω u hu hnonzero
    refine ⟨n, han, huEq, ?_⟩
    simp only [Y, huEq]
