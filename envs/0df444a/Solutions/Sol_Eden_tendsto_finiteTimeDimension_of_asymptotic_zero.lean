-- Prove2me | solution 1 for Eden.tendsto_finiteTimeDimension_of_asymptotic_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:22:13.493216+00:00
-- url     : https://prove2.me/submissions/65942b1b-d77b-47ce-8b9b-cc10ab84fe14

import Definitions.Def_Eden_DimensionConvergenceCriteria
import Definitions.Def_Eden_NeutralDimensionBounds
import Definitions.Def_Eden_LimitingInterpolation
import Definitions.Def_Eden_DimensionConvergence
import Theorems.Thm_Eden_finiteTimeDimension_mem_interval
import Theorems.Thm_Eden_tendsto_finiteTimeDimension_of_eventual_lower_bound


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (p : PhaseSpace)
    (h : asymptoticDimension c p = 0) :
    Tendsto (fun t => finiteTimeDimension c t p) atTop (𝓝 (asymptoticDimension c p)) := by
  apply tendsto_finiteTimeDimension_of_eventual_lower_bound c p
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [h]
  exact (finiteTimeDimension_mem_interval c ht.le p).1
end Eden
