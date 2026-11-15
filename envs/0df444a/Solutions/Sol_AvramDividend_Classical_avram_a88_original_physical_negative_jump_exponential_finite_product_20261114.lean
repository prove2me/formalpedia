-- Prove2me | solution 1 for AvramDividend.Classical.avram_a88_original_physical_negative_jump_exponential_finite_product_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:14:46.563478+00:00
-- url     : https://prove2.me/submissions/882973dd-e3e2-413f-8e50-a9c868c234eb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a66_original_finiteactivity_actual_cumulative_negative_jump_sum_nonpos_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a35_finite_support_causal_marked_tsum_eq_finite_sum_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a53_finite_causal_marked_jump_laplace_exp_eq_product_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (J : Ω → ℝ)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
      else 0) :
    ∀ᵐ ω ∂P,
      ∃ S : Finset ℝ≥0,
        (∀ u, u ∈ S ↔ 0 < u ∧ u ≤ t ∧
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u ≠ 0) ∧
        Real.exp (θ * J ω) =
          ∏ u ∈ S, if u ≤ t then
            Real.exp (θ * (X.X u ω -
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u))
          else 1 := by
  have hFiniteS :=
    avram_a66_original_finiteactivity_actual_cumulative_negative_jump_sum_nonpos_20261114
      X hFinite
  filter_upwards [hFiniteS, hJEq] with ω hSω hJω
  obtain ⟨S, hSupport, _⟩ := hSω t
  refine ⟨S, hSupport, ?_⟩
  have hSum :=
    avram_a35_finite_support_causal_marked_tsum_eq_finite_sum_20261114
      (fun u : ℝ≥0 =>
        X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u)
      t S hSupport t le_rfl
  calc
    Real.exp (θ * J ω) =
        Real.exp (θ * (∑' u : ℝ≥0,
          if 0 < u ∧ u ≤ t then
            X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
          else 0)) := by rw [hJω]
    _ = Real.exp (θ * (∑ u ∈ S,
          if u ≤ t then
            X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
          else 0)) := by rw [hSum]
    _ = ∏ u ∈ S, if u ≤ t then
        Real.exp (θ * (X.X u ω -
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u))
        else 1 := by
      exact
        avram_a53_finite_causal_marked_jump_laplace_exp_eq_product_20261114
          S (fun u : ℝ≥0 =>
            X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u)
          t θ
