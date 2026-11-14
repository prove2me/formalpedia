-- Prove2me | solution 1 for CountingLLL.ContractedWalk.walk3_harmonic_pgf
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:12:38.748832+00:00
-- url     : https://prove2.me/submissions/28a8f4d0-b5a4-4316-82e7-0c6a92cd331e

import Theorems.Thm_CountingLLL_ContractedWalk_harmonic_pgf_integral
import Theorems.Thm_CountingLLL_ContractedWalk_upward_count_real_integrable
import Definitions.Def_CountingLLL_ContractedGF
import Theorems.Thm_CountingLLL_ContractedWalk_generating_function_factor
import Theorems.Thm_CountingLLL_ContractedWalk_upward_count_measurable_integrable
set_option autoImplicit false
open MeasureTheory CountingLLL.ContractedWalk
open scoped ENNReal Interval BigOperators

open CountingLLL.ContractedWalk

private theorem bitLaw_probability' (p : ℝ≥0∞) (hp : p ≤ 1) : IsProbabilityMeasure (bitLaw p) := by
  constructor
  simp only [bitLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact tsub_add_cancel_of_le hp

/-- The harmonic expectation for the walk from level three is the paper's G³ integral. -/
private theorem walk3_harmonic_pgf (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 1/3)
    (hU : Integrable (fun ω : Tape => (upwardCount ω 3 : ℝ)) (tapeLaw (ENNReal.ofReal θ))) :
    (∫ ω : Tape, ∑ k ∈ Finset.range (upwardCount ω 3), (1:ℝ)/(k+2) ∂tapeLaw (ENNReal.ofReal θ)) =
      ∫ z in (0:ℝ)..1, z*(1-(generatingFunction θ z)^3)/(1-z) := by
  have hp : ENNReal.ofReal θ ≤ 1 := by
    have hreal : θ ≤ (1:ℝ) := by linarith
    simpa using ENNReal.ofReal_le_ofReal hreal
  letI : IsProbabilityMeasure (bitLaw (ENNReal.ofReal θ)) := bitLaw_probability' _ hp
  letI : IsProbabilityMeasure (tapeLaw (ENNReal.ofReal θ)) := by unfold tapeLaw; infer_instance
  rw [harmonic_pgf_integral (tapeLaw (ENNReal.ofReal θ)) (fun ω => upwardCount ω 3)
    (upward_count_measurable_integrable.1 3) hU]
  apply intervalIntegral.integral_congr
  intro z hz
  have hz' : z ∈ Set.Icc (0:ℝ) 1 := by simpa using hz
  have f2 := generating_function_factor θ z hθ0 hθ hz'.1 hz'.2 1
  have f3 := generating_function_factor θ z hθ0 hθ hz'.1 hz'.2 2
  change (∫ ω : Tape, z ^ upwardCount ω 2 ∂tapeLaw (ENNReal.ofReal θ)) =
    generatingFunction θ z * generatingFunction θ z at f2
  change (∫ ω : Tape, z ^ upwardCount ω 3 ∂tapeLaw (ENNReal.ofReal θ)) =
    generatingFunction θ z * (∫ ω : Tape, z ^ upwardCount ω 2 ∂tapeLaw (ENNReal.ofReal θ)) at f3
  rw [f2] at f3
  dsimp only
  rw [f3]
  ring

/-- The source harmonic-to-generating-function identity, without auxiliary assumptions. -/
theorem solution (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 1/3) :
    (∫ ω : Tape, ∑ k ∈ Finset.range (upwardCount ω 3), (1:ℝ)/(k+2) ∂tapeLaw (ENNReal.ofReal θ)) =
      ∫ z in (0:ℝ)..1, z*(1-(generatingFunction θ z)^3)/(1-z) :=
  walk3_harmonic_pgf θ hθ0 hθ (upward_count_real_integrable θ hθ0 hθ 3)
