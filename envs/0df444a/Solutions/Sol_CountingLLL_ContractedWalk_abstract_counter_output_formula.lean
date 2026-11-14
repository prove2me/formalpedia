-- Prove2me | solution 1 for CountingLLL.ContractedWalk.abstract_counter_output_formula
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:26:04.900769+00:00
-- url     : https://prove2.me/submissions/96b62949-3808-43bf-816c-ef06e789c1ef

import Definitions.Def_CountingLLL_ContractedGF
import Theorems.Thm_CountingLLL_ContractedWalk_pgf_reciprocal_expectation
import Theorems.Thm_CountingLLL_ContractedWalk_initial_counter_generating_function
import Theorems.Thm_CountingLLL_ContractedWalk_counter_integral_correctness
import Theorems.Thm_CountingLLL_ReciprocalTest_source_parameter_bounds
import Theorems.Thm_CountingLLL_ContractedWalk_upward_count_measurable_integrable

set_option autoImplicit false
open MeasureTheory CountingLLL.ContractedWalk
open scoped ENNReal Interval

private theorem bitLaw_probability' (p : ℝ≥0∞) (hp : p ≤ 1) : IsProbabilityMeasure (bitLaw p) := by
  constructor
  simp only [bitLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact tsub_add_cancel_of_le hp

theorem solution (B : ℝ) (hB0 : 0 < B) (hB1 : B < 1) (hB : Real.exp (-(3/10 : ℝ)) ≤ B) :
    let u := 2*(1-B)/(2-B)
    let θ := u^2/(1-u+u^2)
    let ν := (bitLaw (ENNReal.ofReal u)).prod (tapeLaw (ENNReal.ofReal θ))
    1-(∫ x : Bool × Tape, (1:ℝ)/(((if x.1 then 1 + upwardCount x.2 3 else upwardCount x.2 1) : ℕ) + 1 : ℝ) ∂ν)/2 = 1/(2*B) := by
  let u : ℝ := 2*(1-B)/(2-B)
  let θ : ℝ := u^2/(1-u+u^2)
  have huθ := CountingLLL.ReciprocalTest.source_parameter_bounds B hB (by linarith)
  change 0 ≤ u ∧ u < 33/80 ∧ 0 ≤ θ ∧ θ < 9/40 at huθ
  have hu0 : 0 ≤ u := huθ.1
  have hu1 : u ≤ 1 := by linarith [huθ.2.1]
  have ht0 : 0 ≤ θ := huθ.2.2.1
  have ht : θ < 1/3 := by linarith [huθ.2.2.2]
  have hp : ENNReal.ofReal u ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal hu1
  have hq : ENNReal.ofReal θ ≤ 1 := by
    have hh : θ ≤ (1:ℝ) := by linarith
    simpa using ENNReal.ofReal_le_ofReal hh
  letI : IsProbabilityMeasure (bitLaw (ENNReal.ofReal u)) := bitLaw_probability' _ hp
  letI : IsProbabilityMeasure (bitLaw (ENNReal.ofReal θ)) := bitLaw_probability' _ hq
  letI : IsProbabilityMeasure (tapeLaw (ENNReal.ofReal θ)) := by unfold tapeLaw; infer_instance
  let ν := (bitLaw (ENNReal.ofReal u)).prod (tapeLaw (ENNReal.ofReal θ))
  letI : IsProbabilityMeasure ν := inferInstance
  let K : Bool × Tape → ℕ := fun x => if x.1 then 1+upwardCount x.2 3 else upwardCount x.2 1
  have hK : Measurable K := by
    apply Measurable.ite ((MeasurableSet.singleton true).preimage measurable_fst)
    · exact measurable_const.add ((upward_count_measurable_integrable.1 3).comp measurable_snd)
    · exact (upward_count_measurable_integrable.1 1).comp measurable_snd
  have hPGF := pgf_reciprocal_expectation ν K hK
  have hfunc : (∫ z in (0:ℝ)..1, ∫ x : Bool × Tape, z ^ K x ∂ν) =
      ∫ z in (0:ℝ)..1, ((1-u)*generatingFunction θ z + u*z*(generatingFunction θ z)^3) := by
    apply intervalIntegral.integral_congr
    intro z hz
    have hz' : z ∈ Set.Icc (0:ℝ) 1 := by simpa using hz
    exact initial_counter_generating_function u θ z hu0 hu1 ht0 ht hz'.1 hz'.2
  rw [hfunc] at hPGF
  have hresult := counter_integral_correctness B hB0 hB1 hB
  change 1 - (∫ z in (0:ℝ)..1, ((1-u)*generatingFunction θ z + u*z*(generatingFunction θ z)^3))/2 = 1/(2*B) at hresult
  change 1-(∫ x : Bool × Tape, (1:ℝ)/((K x : ℝ)+1) ∂ν)/2 = 1/(2*B)
  rw [hPGF]
  exact hresult
