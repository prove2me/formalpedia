-- Prove2me | solution 1 for Eden.tendsto_finiteTimeDimension_of_eventual_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:21:13.943996+00:00
-- url     : https://prove2.me/submissions/59a15565-8d25-4c6d-8fa5-c92600693bc7

import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_DimensionConvergenceCriteria
import Theorems.Thm_Eden_tendsto_finiteTimeDimension_of_lower_tests

set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (p : PhaseSpace)
    (hlo : ∀ᶠ t in atTop, asymptoticDimension c p ≤ finiteTimeDimension c t p) :
    Tendsto (fun t => finiteTimeDimension c t p) atTop (𝓝 (asymptoticDimension c p)) := by
  apply tendsto_finiteTimeDimension_of_lower_tests c p
  intro d hd
  filter_upwards [hlo] with t ht
  exact hd.2.le.trans ht
end Eden
