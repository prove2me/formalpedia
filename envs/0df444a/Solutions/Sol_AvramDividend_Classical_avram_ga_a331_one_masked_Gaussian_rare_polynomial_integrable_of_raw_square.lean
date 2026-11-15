-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a331_one_masked_Gaussian_rare_polynomial_integrable_of_raw_square
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:20:03.224522+00:00
-- url     : https://prove2.me/submissions/ac3f95c9-3ef8-4fb8-ba71-c05e7ec062f1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a310_raw_centered_Gaussian_polynomial_bounded_by_raw_square
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (r : Ω → ℝ) (a δ : ℝ)
    (A : Ω → Prop) [DecidablePred A] (hAm : MeasurableSet {ω | A ω})
    (hrm : Measurable r) (hRawI : Integrable
      (fun ω => if A ω then (r ω)^2 else 0) P) :
    Integrable (fun ω =>
      if A ω ∧ δ ≤ |r ω| then
        1+|r ω|+(r ω-a)^2/2 else 0) P := by
  let B : Ω → ℝ := fun ω =>
    2 * (if A ω then (r ω)^2 else 0) + (a^2 + 2)
  have hB : Integrable B P := by
    exact (hRawI.const_mul 2).add (integrable_const (a^2 + 2))
  have hMeas : Measurable (fun ω : Ω =>
      if A ω ∧ δ ≤ |r ω| then
        1 + |r ω| + (r ω - a)^2/2 else 0) := by
    apply Measurable.ite
    · exact hAm.inter (measurableSet_le measurable_const hrm.abs)
    · fun_prop
    · exact measurable_const
  apply Integrable.mono' hB hMeas.aestronglyMeasurable
  filter_upwards [] with ω
  by_cases hA : A ω
  · by_cases hδ : δ ≤ |r ω|
    · simp only [hA, hδ, and_self, and_true, ite_true]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact (avram_ga_a310_raw_centered_Gaussian_polynomial_bounded_by_raw_square
        (r ω) a).trans_eq (by simp [B, hA] <;> ring)
    · simp [hA, hδ, B]
      positivity
  · simp [hA, B]
    positivity
