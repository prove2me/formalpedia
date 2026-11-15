-- Prove2me | solution 1 for AvramDividend.Classical.avram_a36_original_intrinsic_gaussian_limit_continuous_on_each_horizon_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:15:29.474205+00:00
-- url     : https://prove2.me/submissions/a9de9709-5c7a-4919-8107-78cc3a3a2fd3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a33_original_finiteactivity_jumpremoved_source_continuous_horizon_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a35_original_intrinsic_gaussian_equals_minus_true_jump_series_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a35_finite_support_causal_marked_tsum_eq_finite_sum_20261114
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
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      ContinuousOn (fun t : ℝ≥0 => R t ω) (Iic T) := by
  have hSource :=
    avram_a33_original_finiteactivity_jumpremoved_source_continuous_horizon_20261114
      X hFinite
  have hIdentity :=
    avram_a35_original_intrinsic_gaussian_equals_minus_true_jump_series_20261114
      X hFinite R hR
  filter_upwards [hSource, hIdentity] with ω hSω hRω
  intro T
  let f : ℝ≥0 → ℝ := fun t => X.X t ω
  let j : ℝ≥0 → ℝ := fun t => f t - Function.leftLim f t
  let d : ℝ := X.c - ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν
  obtain ⟨S, hS, hCont⟩ := hSω T
  have hFiniteSum :=
    avram_a35_finite_support_causal_marked_tsum_eq_finite_sum_20261114
      j T S hS
  have hEq (t : ℝ≥0) (ht : t ∈ Iic T) :
      R t ω =
        (f t - ∑ u ∈ S, if u ≤ t then j u else 0) -
        (t : ℝ) * d := by
    have hMarked := hFiniteSum t ht
    have hExact := hRω t
    dsimp [f, j, d] at hMarked hExact ⊢
    rw [hMarked] at hExact
    linarith
  have hBase : ContinuousOn
      (fun t : ℝ≥0 => f t - ∑ u ∈ S, if u ≤ t then j u else 0)
      (Iic T) := by
    intro t ht
    exact (hCont t ht).continuousWithinAt
  have hDrift : Continuous (fun t : ℝ≥0 => (t : ℝ) * d) := by
    fun_prop
  have hTarget : ContinuousOn
      (fun t : ℝ≥0 =>
        (f t - ∑ u ∈ S, if u ≤ t then j u else 0) -
        (t : ℝ) * d) (Iic T) :=
    hBase.sub hDrift.continuousOn
  apply hTarget.congr
  intro t ht
  exact hEq t ht
