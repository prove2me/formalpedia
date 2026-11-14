-- Prove2me | solution 1 for CountingLLL.ContractedWalk.counter_integral_correctness
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:23:17.600293+00:00
-- url     : https://prove2.me/submissions/d2dd3721-5bdc-45b9-8715-2943a3fde4e7

import Definitions.Def_CountingLLL_ContractedGF
import Theorems.Thm_CountingLLL_ContractedWalk_generating_function_recursion
import Theorems.Thm_CountingLLL_ContractedWalk_generating_function_integral
import Theorems.Thm_CountingLLL_ContractedWalk_generating_function_continuous
import Theorems.Thm_CountingLLL_ReciprocalTest_source_accuracy_algebra
import Theorems.Thm_CountingLLL_ReciprocalTest_source_parameter_bounds

set_option autoImplicit false
open MeasureTheory CountingLLL.ContractedWalk
open scoped Interval

noncomputable section

theorem solution (B : ℝ) (hB0 : 0 < B) (hB1 : B < 1)
    (hB : Real.exp (-(3/10 : ℝ)) ≤ B) :
    let u := 2*(1-B)/(2-B)
    let θ := u^2/(1-u+u^2)
    1 - (∫ z in (0:ℝ)..1, ((1-u)*generatingFunction θ z + u*z*(generatingFunction θ z)^3))/2 = 1/(2*B) := by
  let u : ℝ := 2*(1-B)/(2-B)
  let θ : ℝ := u^2/(1-u+u^2)
  have huθ := CountingLLL.ReciprocalTest.source_parameter_bounds B hB (by linarith)
  change 0 ≤ u ∧ u < 33/80 ∧ 0 ≤ θ ∧ θ < 9/40 at huθ
  have ht0 : 0 ≤ θ := huθ.2.2.1
  have ht : θ < 1/3 := by linarith [huθ.2.2.2]
  have hu : 0 < u := by
    have h1 : 0 < 1-B := by linarith
    have h2 : 0 < 2-B := by linarith
    dsimp [u]
    exact div_pos (mul_pos (by norm_num) h1) h2
  have hden : 0 < 1-u+u^2 := by have := sq_nonneg u; linarith [huθ.2.1]
  have htpos : 0 < θ := by dsimp [θ]; exact div_pos (sq_pos_of_pos hu) hden
  have hθne : θ ≠ 0 := ne_of_gt htpos
  have hGcont : ContinuousOn (generatingFunction θ) [[(0:ℝ),1]] := by
    simpa using generating_function_continuous θ ht0 ht
  have hI : IntervalIntegrable (generatingFunction θ) volume 0 1 := hGcont.intervalIntegrable
  have hI' : IntervalIntegrable (fun z => generatingFunction θ z - (1-θ)) volume 0 1 :=
    hI.sub intervalIntegrable_const
  have hleft : IntervalIntegrable (fun z => (1-u)*generatingFunction θ z) volume 0 1 := hI.const_mul _
  have hright : IntervalIntegrable (fun z => (u/θ)*(generatingFunction θ z - (1-θ))) volume 0 1 := hI'.const_mul _
  have hpoint : Set.EqOn (fun z => (1-u)*generatingFunction θ z + u*z*(generatingFunction θ z)^3)
      (fun z => (1-u)*generatingFunction θ z + (u/θ)*(generatingFunction θ z - (1-θ))) [[(0:ℝ),1]] := by
    intro z hz
    have hz' : z ∈ Set.Icc (0:ℝ) 1 := by simpa using hz
    have hc := generating_function_recursion θ z ht0 ht hz'.1 hz'.2
    field_simp
    <;> nlinarith
  change 1 - (∫ z in (0:ℝ)..1, ((1-u)*generatingFunction θ z + u*z*(generatingFunction θ z)^3))/2 = 1/(2*B)
  rw [intervalIntegral.integral_congr hpoint, intervalIntegral.integral_add hleft hright]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hI intervalIntegrable_const]
  simp only [intervalIntegral.integral_const, sub_zero, one_smul]
  rw [generating_function_integral θ ht0 ht]
  have hs := CountingLLL.ReciprocalTest.source_accuracy_algebra B hB0 hB1
  change 1-((1-u)*(1-θ/(2*(1-θ))) + u*((1-θ/(2*(1-θ)))-1+θ)/θ)/2 = 1/(2*B) at hs
  convert hs using 1 <;> ring
