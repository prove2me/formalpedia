-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a546_zerojump_generator_positive_interior_measurable_extension
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:07:59.670132+00:00
-- url     : https://prove2.me/submissions/09aebb7e-d807-48e6-8428-e419ded7c240

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f11_zero_jump_generator_eq_gaussian_drift
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_measurable_cap_interior_deriv_zero_extension
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_measurable_cap_interior_iteratedDeriv_two_zero_extension
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    Measurable (fun y : ℝ =>
      if 0 < y ∧ ENNReal.ofReal y < C then X.generator w y else 0) := by
  classical
  have hgrad :=
    avram_wave4_04b_measurable_cap_interior_deriv_zero_extension w C hw
  have hhess :=
    avram_wave5_03a_measurable_cap_interior_iteratedDeriv_two_zero_extension w C hw
  have heq : (fun y : ℝ =>
      if 0 < y ∧ ENNReal.ofReal y < C then X.generator w y else 0) =
      (fun y : ℝ =>
        X.σ ^ 2 / 2 * (if 0 < y ∧ ENNReal.ofReal y < C then
          iteratedDeriv 2 w y else 0) +
        X.c * (if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0)) := by
    funext y
    by_cases hp : 0 < y ∧ ENNReal.ofReal y < C
    · simp only [if_pos hp]
      rw [avram_p4_f11_zero_jump_generator_eq_gaussian_drift X hν]
    · simp [hp]
  rw [heq]
  exact (measurable_const.mul hhess).add (measurable_const.mul hgrad)
