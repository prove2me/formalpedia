-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_physical_marked_cell_coefficients_subprobability_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T23:59:05.866994+00:00
-- url     : https://prove2.me/submissions/0f0e299e-91d5-4571-826f-9d31faa8e233

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a85_original_physical_negative_jump_exponential_integrable_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a107_original_physical_negative_jump_exponential_expectation_unit_bound_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a27_integral_eq_hasSum_exact_nat_count_cell_integrals_20261117
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
      else 0)
    (K : Ω → ℕ) (hK : Measurable K) :
    (∀ k : ℕ, 0 ≤
      (∫ ω in {ω : Ω | K ω = k}, Real.exp (θ * J ω) ∂P)) ∧
    HasSum (fun k : ℕ =>
      (∫ ω in {ω : Ω | K ω = k}, Real.exp (θ * J ω) ∂P))
      (∫ ω, Real.exp (θ * J ω) ∂P) ∧
    (∫ ω, Real.exp (θ * J ω) ∂P) ≤ 1 := by
  have hIntegrable :=
    (avram_a85_original_physical_negative_jump_exponential_integrable_20261114
      X hFinite t θ hθ J hJMeas hJEq).1
  constructor
  · intro k
    exact integral_nonneg (fun ω =>
      le_of_lt (Real.exp_pos (θ * J ω)))
  constructor
  · exact
      avram_a27_integral_eq_hasSum_exact_nat_count_cell_integrals_20261117
        P K hK (fun ω => Real.exp (θ * J ω)) hIntegrable
  · exact
      avram_a107_original_physical_negative_jump_exponential_expectation_unit_bound_20261114
        X hFinite t θ hθ J hJMeas hJEq
