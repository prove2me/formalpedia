-- Prove2me | solution 1 for BlackScholesModel.stdNormalCDF_upper_tail_le_pdf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T16:11:45.705951+00:00
-- url     : https://prove2.me/submissions/1acc733a-64c1-4713-925b-d58bb6845b5a

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Theorems.Thm_BlackScholesModel_stdNormalCDF_hasDerivAt
import Theorems.Thm_BlackScholesModel_stdNormalPDF_hasDerivAt
import Theorems.Thm_BlackScholesModel_stdNormalCDF_tail_limits
import Theorems.Thm_BlackScholesModel_stdNormalPDF_tendsto_zero_atTop
import Theorems.Thm_BlackScholesModel_stdNormalCDF_neg

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

/-- Mills upper bound on the normal upper tail for x at least one. -/
theorem solution (x : ℝ) (hx : 1 ≤ x) :
    0 ≤ 1 - stdNormalCDF x ∧
    1 - stdNormalCDF x ≤ stdNormalPDF x := by
  let H : ℝ → ℝ := fun y => stdNormalCDF y + stdNormalPDF y
  have hH_deriv (y : ℝ) :
      HasDerivAt H ((1 - y) * stdNormalPDF y) y := by
    convert (stdNormalCDF_hasDerivAt y).add
      (stdNormalPDF_hasDerivAt y) using 1 <;>
        first
        | rfl
        | ring
  have hH_diff : Differentiable ℝ H := by
    intro y
    exact (hH_deriv y).differentiableAt
  have hH_antitone : AntitoneOn H (Set.Ici (1 : ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 1)
      hH_diff.continuous.continuousOn
      hH_diff.differentiableOn
    intro y hy
    have hy1 : 1 ≤ y := by
      have hy' : (1 : ℝ) < y := by
        simpa only [interior_Ici, Set.mem_Ioi] using hy
      exact le_of_lt hy'
    rw [(hH_deriv y).deriv]
    apply mul_nonpos_of_nonpos_of_nonneg
    · linarith
    · unfold stdNormalPDF
      positivity
  have hH_limit : Tendsto H atTop (𝓝 1) := by
    simpa only [H, add_zero] using
      stdNormalCDF_tail_limits.2.add stdNormalPDF_tendsto_zero_atTop
  have hevent : (fun y : ℝ => H y) ≤ᶠ[atTop]
      (fun _ : ℝ => H x) := by
    filter_upwards [Filter.eventually_ge_atTop x] with y hxy
    apply hH_antitone
    · exact hx
    · exact le_trans hx hxy
    · exact hxy
  have hlimit : 1 ≤ H x :=
    tendsto_le_of_eventuallyLE hH_limit tendsto_const_nhds hevent
  have hupper : 1 - stdNormalCDF x ≤ stdNormalPDF x := by
    dsimp [H] at hlimit
    linarith
  have hnormal_nonneg : 0 ≤ stdNormalCDF (-x) := by
    have hint : 0 ≤ ∫ z in Set.Iic (-x), Real.exp (-z ^ 2 / 2) := by
      apply integral_nonneg
      intro z
      exact (Real.exp_pos _).le
    unfold stdNormalCDF
    exact mul_nonneg (by positivity) hint
  have htail_nonneg : 0 ≤ 1 - stdNormalCDF x := by
    simpa only [stdNormalCDF_neg] using hnormal_nonneg
  exact ⟨htail_nonneg, hupper⟩
