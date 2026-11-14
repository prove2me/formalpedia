-- Prove2me | solution 1 for CountingLLL.ContractedWalk.generating_function_bounds
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:46:42.6273+00:00
-- url     : https://prove2.me/submissions/46dc93d1-700f-4b10-a383-cae7485a52ab

import Definitions.Def_CountingLLL_ContractedGF
import Theorems.Thm_CountingLLL_ContractedWalk_upward_count_measurable_integrable

set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ContractedWalk
open scoped ENNReal

private theorem bitLaw_probability' (p : ℝ≥0∞) (hp : p ≤ 1) : IsProbabilityMeasure (bitLaw p) := by
  constructor
  simp only [bitLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact tsub_add_cancel_of_le hp

theorem solution (θ z : ℝ) (hθ : θ ≤ 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ generatingFunction θ z ∧ generatingFunction θ z ≤ 1 := by
  have hp : ENNReal.ofReal θ ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal hθ
  letI : IsProbabilityMeasure (bitLaw (ENNReal.ofReal θ)) := bitLaw_probability' _ hp
  letI : IsProbabilityMeasure (tapeLaw (ENNReal.ofReal θ)) := by unfold tapeLaw; infer_instance
  have hInt := upward_count_measurable_integrable.2 θ z hθ hz0 hz1 1
  constructor
  · exact integral_nonneg (fun ω => pow_nonneg hz0 _)
  · have h := integral_mono hInt (integrable_const (1:ℝ)) (fun ω => pow_le_one₀ hz0 hz1)
    simpa [generatingFunction] using h
