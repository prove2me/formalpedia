-- Prove2me | solution 1 for CountingLLL.ContractedWalk.source_M_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:17:44.120101+00:00
-- url     : https://prove2.me/submissions/63a5e4ae-3b6d-4221-8b88-20f2ea98a7ea

import Definitions.Def_CountingLLL_ContractedCost
import Definitions.Def_CountingLLL_ContractedGF
import Theorems.Thm_CountingLLL_ContractedWalk_absorption_and_expected_changes
import Theorems.Thm_CountingLLL_ContractedWalk_upward_count_measurable_integrable
import Theorems.Thm_CountingLLL_ContractedWalk_generating_function_recursion
import Theorems.Thm_CountingLLL_ContractedWalk_generating_function_bounds
import Theorems.Thm_CountingLLL_ContractedWalk_cost_harmonic_expectation
import Theorems.Thm_CountingLLL_ContractedWalk_walk3_harmonic_pgf
import Theorems.Thm_CountingLLL_ContractedWalk_harmonic_ennreal_eq_ofReal
import Theorems.Thm_CountingLLL_ContractedWalk_upward_count_real_integrable
import Theorems.Thm_CountingLLL_ContractedWalk_generating_cost_bound
import Theorems.Thm_CountingLLL_ContractedWalk_weighted_cost_finite
import Theorems.Thm_CountingLLL_ContractedWalk_source_M_zero
set_option autoImplicit false
open MeasureTheory CountingLLL.ContractedWalk
open scoped ENNReal Interval BigOperators

private theorem source_integrand (θ z : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 9/40)
    (hz0 : 0 ≤ z) (hz1 : z < 1) :
    let g := generatingFunction θ z
    z*(1-g^3)/(1-z) = θ*(z*(1+g+g^2)/(1-θ*z*(1+g+g^2))) := by
  let g := generatingFunction θ z
  have hg := generating_function_bounds θ z (by linarith) hz0 (by linarith)
  change 0 ≤ g ∧ g ≤ 1 at hg
  have hc := generating_function_recursion θ z (by linarith) (by linarith) hz0 (by linarith)
  change g = 1-θ+θ*z*g^3 at hc
  have ha1 : 1+g+g^2 ≤ 3 := by nlinarith [sq_nonneg (g-1)]
  have hθz : 0 ≤ θ*z := by positivity
  have hh : θ*z*(1+g+g^2) ≤ 3*θ*z := by nlinarith [mul_nonneg hθz (sub_nonneg.mpr ha1)]
  have ht : θ*z ≤ θ := by nlinarith [mul_nonneg (le_of_lt hθ0) (sub_nonneg.mpr (le_of_lt hz1))]
  have hd : 0 < 1-θ*z*(1+g+g^2) := by linarith
  have hz' : 0 < 1-z := by linarith
  change z*(1-g^3)/(1-z) = θ*(z*(1+g+g^2)/(1-θ*z*(1+g+g^2)))
  have hd' : 1-z*θ*(1+g+g^2) ≠ 0 := by nlinarith [hd]
  field_simp [ne_of_gt hz', ne_of_gt hd, hd']
  nlinarith [hc]

private theorem source_integrals (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 9/40) :
    (∫ z in (0:ℝ)..1, z*(1-(generatingFunction θ z)^3)/(1-z)) =
      θ*(∫ z in (0:ℝ)..1, z*(1+generatingFunction θ z+(generatingFunction θ z)^2)/
      (1-θ*z*(1+generatingFunction θ z+(generatingFunction θ z)^2))) := by
  rw [← intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae ((volume : Measure ℝ).ae_ne (1:ℝ))] with z hz hz1
  exact source_integrand θ z hθ0 hθ1 (le_of_lt hz.1) (lt_of_le_of_ne hz.2 hz1)

private theorem bitLaw_probability' (p : ℝ≥0∞) (hp : p ≤ 1) : IsProbabilityMeasure (bitLaw p) := by
  constructor
  simp only [bitLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact tsub_add_cancel_of_le hp

/-- The exact strict source bound for the weighted-change quantity M. -/
theorem solution (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 9/40) :
    expectedWeightedChanges (ENNReal.ofReal θ) 3 2 < ENNReal.ofReal (74/25 : ℝ) := by
  by_cases hzero : θ = 0
  · subst θ
    rw [ENNReal.ofReal_zero, source_M_zero]
    apply (ENNReal.toReal_lt_toReal (by finiteness) ENNReal.ofReal_ne_top).mp
    norm_num [ENNReal.toReal_div]
  · have hp0 : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hzero)
    have hθ3 : θ < 1/3 := by linarith
    have hp : ENNReal.ofReal θ ≤ 1 := by
      have hh : θ ≤ (1:ℝ) := by linarith
      simpa using ENNReal.ofReal_le_ofReal hh
    letI : IsProbabilityMeasure (bitLaw (ENNReal.ofReal θ)) := bitLaw_probability' _ hp
    letI : IsProbabilityMeasure (tapeLaw (ENNReal.ofReal θ)) := by unfold tapeLaw; infer_instance
    let μ := tapeLaw (ENNReal.ofReal θ)
    let K : Tape → ℕ := fun ω => upwardCount ω 3
    have hK : Measurable K := upward_count_measurable_integrable.1 3
    have hKi : Integrable (fun ω => (K ω : ℝ)) μ := upward_count_real_integrable θ hθ0 hθ3 3
    have hconv := harmonic_ennreal_eq_ofReal μ K hK hKi
    have hmh := cost_harmonic_expectation θ hθ0 hθ3
    change expectedWeightedChanges (ENNReal.ofReal θ) 3 2 * ENNReal.ofReal θ =
      ∫⁻ ω, ∑ k ∈ Finset.range (K ω), (((2+k : ℕ) : ℝ≥0∞)⁻¹) ∂μ at hmh
    have hsum : ∀ ω, (∑ k ∈ Finset.range (K ω), (((2+k : ℕ) : ℝ≥0∞)⁻¹)) =
        ∑ k ∈ Finset.range (K ω), (((k+2 : ℕ) : ℝ≥0∞)⁻¹) := by intro ω; congr 1; ext k; simp [Nat.add_comm]
    simp_rw [hsum] at hmh
    rw [hconv] at hmh
    have hH0 : 0 ≤ (∫ ω, ∑ k ∈ Finset.range (K ω), (1:ℝ)/(k+2) ∂μ) := by
      apply integral_nonneg
      intro ω
      exact Finset.sum_nonneg (fun k hk => by positivity)
    have hreal := congrArg ENNReal.toReal hmh
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ0, ENNReal.toReal_ofReal hH0] at hreal
    have hform := walk3_harmonic_pgf θ hθ0 hθ3
    change (∫ ω, ∑ k ∈ Finset.range (K ω), (1:ℝ)/(k+2) ∂μ) = _ at hform
    rw [source_integrals θ hp0 hθ1] at hform
    rw [hform] at hreal
    have hident : (expectedWeightedChanges (ENNReal.ofReal θ) 3 2).toReal =
      ∫ z in (0:ℝ)..1, z*(1+generatingFunction θ z+(generatingFunction θ z)^2)/
      (1-θ*z*(1+generatingFunction θ z+(generatingFunction θ z)^2)) := by nlinarith
    have hbound := generating_cost_bound θ hθ0 hθ1
    have hfinite : expectedWeightedChanges (ENNReal.ofReal θ) 3 2 ≠ ⊤ := by
      have hh := weighted_cost_finite θ hθ0 hθ3 3 2 (by omega)
      exact ne_of_lt (lt_of_le_of_lt hh ENNReal.ofReal_lt_top)
    apply (ENNReal.toReal_lt_toReal hfinite ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 74/25), hident]
    exact hbound
