-- Prove2me | solution 1 for AvramDividend.Classical.avram_a50_original_physical_levy_exponential_gaussian_jump_drift_factorisation_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:51:02.332224+00:00
-- url     : https://prove2.me/submissions/764f091b-06e3-4f80-a497-54e6791cfb94

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a35_original_intrinsic_gaussian_equals_minus_true_jump_series_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∀ᵐ ω ∂P, ∀ (t : ℝ≥0) (θ : ℝ),
      Real.exp (θ * X.X t ω) =
        Real.exp (θ * R t ω) *
        Real.exp (θ * ((t : ℝ) *
          (X.c - ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν))) *
        Real.exp (θ * (∑' u : ℝ≥0,
          if 0 < u ∧ u ≤ t then
            X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
          else 0)) := by
  have hSource :=
    avram_a35_original_intrinsic_gaussian_equals_minus_true_jump_series_20261114
      X hFinite R hR
  filter_upwards [hSource] with ω hω
  intro t θ
  have hPath := hω t
  have hSplit : X.X t ω =
      R t ω +
      (t : ℝ) * (X.c - ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) +
      (∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
        else 0) := by
    linarith
  rw [hSplit]
  simp only [mul_add, Real.exp_add]
