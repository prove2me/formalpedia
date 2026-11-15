-- Prove2me | solution 1 for AvramDividend.Classical.avram_a99_original_measurable_physical_marked_jump_measure_dirac_enumeration_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:45:46.980414+00:00
-- url     : https://prove2.me/submissions/847ac524-9c5c-41b1-ad88-0d1b4f37931c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_original_measurable_jump_enumeration
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_jump_measure_eq_distinct_enumerated_diracs
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
      (∀ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) =
        Measure.sum (fun n => (A n).indicator
          (fun _ => Measure.dirac (T n ω, Y n ω)) ω)) := by
  obtain ⟨T, A, hT, hA, hActive, hInject, hCover⟩ :=
    avram_wave5_02a_actual_original_measurable_jump_enumeration X
  let Y : ℕ → Ω → ℝ := fun n ω =>
    X.X (T n ω) ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) (T n ω)
  have hJoint :=
    avram_wave4_04a_actual_levy_jumpmark_joint_measurable X
  have hYm (n : ℕ) : Measurable (Y n) :=
    hJoint.comp ((hT n).prodMk measurable_id)
  refine ⟨T, A, Y, hT, hA, hYm, ?_⟩
  intro ω
  simpa only [Y] using
    (avram_wave5_02a_actual_jump_measure_eq_distinct_enumerated_diracs
      X T A hActive hInject hCover ω)
