-- Prove2me | solution 1 for BlackScholesModel.stdNormalPDF_tendsto_zero_atTop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T16:11:49.27785+00:00
-- url     : https://prove2.me/submissions/4cab82ef-12d0-4411-8c3f-1162673236a1

import Mathlib
import Definitions.Def_BlackScholesModel_Core

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

/-- Gaussian density decays to zero as its argument tends to infinity. -/
theorem solution : Tendsto stdNormalPDF atTop (𝓝 0) := by
  have hsquare : Tendsto (fun x : ℝ => x ^ 2) atTop atTop :=
    Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have hhalf : Tendsto (fun x : ℝ => (1 / 2 : ℝ) * x ^ 2)
      atTop atTop := hsquare.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  have harg_eq :
      (fun x : ℝ => -(x ^ 2 / 2)) =
      (fun x : ℝ => -((1 / 2 : ℝ) * x ^ 2)) := by
    funext x
    ring
  have hneg : Tendsto (fun x : ℝ => -(x ^ 2 / 2)) atTop atBot := by
    rw [harg_eq]
    simpa only [Function.comp_def] using
      Filter.tendsto_neg_atTop_atBot.comp hhalf
  have hexp : Tendsto (fun x : ℝ => Real.exp (-(x ^ 2 / 2)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def] using Real.tendsto_exp_atBot.comp hneg
  have hpdf := hexp.const_mul (1 / Real.sqrt (2 * Real.pi))
  convert hpdf using 1 <;>
    first
    | rfl
    | (funext x; simp only [stdNormalPDF]; ring)
    | simp