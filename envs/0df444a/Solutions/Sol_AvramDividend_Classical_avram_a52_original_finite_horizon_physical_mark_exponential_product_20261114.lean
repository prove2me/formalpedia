-- Prove2me | solution 1 for AvramDividend.Classical.avram_a52_original_finite_horizon_physical_mark_exponential_product_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:53:04.586515+00:00
-- url     : https://prove2.me/submissions/c76c6d60-09dc-43a1-9bac-6fb4d88750da

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a50_original_physical_levy_exponential_gaussian_jump_drift_factorisation_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a33_original_finiteactivity_jumpremoved_source_continuous_horizon_20261114
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
      let j : ℝ≥0 → ℝ := fun u =>
        X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
      ∃ S : Finset ℝ≥0,
        (∀ u, u ∈ S ↔ 0 < u ∧ u ≤ T ∧ j u ≠ 0) ∧
        (∀ (t : ℝ≥0), t ≤ T → ∀ θ : ℝ,
          Real.exp (θ * X.X t ω) =
            Real.exp (θ * R t ω) *
            Real.exp (θ * ((t : ℝ) *
              (X.c - ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν))) *
            Real.exp (θ * (∑ u ∈ S, if u ≤ t then j u else 0))) := by
  have hFactor :=
    avram_a50_original_physical_levy_exponential_gaussian_jump_drift_factorisation_20261114
      X hFinite R hR
  have hSource :=
    avram_a33_original_finiteactivity_jumpremoved_source_continuous_horizon_20261114
      X hFinite
  filter_upwards [hFactor, hSource] with ω hFω hSω
  intro T
  let j : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
  obtain ⟨S, hS, _⟩ := hSω T
  have hFiniteSum :=
    avram_a35_finite_support_causal_marked_tsum_eq_finite_sum_20261114
      j T S hS
  refine ⟨S, hS, ?_⟩
  intro t ht θ
  have hEq := hFω t θ
  dsimp [j] at hFiniteSum ⊢
  rw [hFiniteSum t ht] at hEq
  exact hEq
