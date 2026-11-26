-- Prove2me | solution 1 for Eden.globalGrowthRate_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:59:41.268938+00:00
-- url     : https://prove2.me/submissions/ae96ccce-abe6-40af-b7d0-84bf78e880f6

import Definitions.Def_Eden_GlobalGrowthLimits
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_OrderedStationarySpectrum
import Definitions.Def_Eden_ExactGlobalGrowth
import Theorems.Thm_Eden_globalLogGrowth_four

set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 ≤ c) : globalGrowthRate c 4 = 4 := by
  apply Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [globalLogGrowth_four hc ht.le, mul_div_cancel_right₀ _ ht.ne']
end Eden
