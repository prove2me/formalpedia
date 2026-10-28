-- Prove2me | solution 1 for FinancialDerivatives.FD06.heatFlow_initial_limit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:13:31.416564+00:00
-- url     : https://prove2.me/submissions/ad3c2243-078e-48ec-a871-dc9206256da2

import Mathlib
import Definitions.Def_fd06_gaussianHeatFlow

open FinancialDerivatives.FD06

theorem solution (f : ℝ → ℝ) (M : ℝ) (hf : Continuous f) (hb : ∀ x, |f x| ≤ M) (x : ℝ) : Filter.Tendsto (fun τ : ℝ => gaussianHeatFlow f τ x) (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x)) := by
  unfold gaussianHeatFlow
  have hlim : (∫ _z : ℝ, f x ∂ProbabilityTheory.gaussianReal 0 1) = f x := by simp
  rw [← hlim]
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence (fun _ => M) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun τ =>
      (hf.comp (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun τ => Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hb _
  · exact MeasureTheory.integrable_const M
  · refine Filter.Eventually.of_forall fun z => ?_
    have hc : Continuous (fun τ : ℝ => f (x + Real.sqrt (2 * τ) * z)) := by fun_prop
    have := hc.tendsto 0
    simp only [mul_zero, Real.sqrt_zero, zero_mul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
