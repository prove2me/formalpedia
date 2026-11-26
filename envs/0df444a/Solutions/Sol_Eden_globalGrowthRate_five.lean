-- Prove2me | solution 1 for Eden.globalGrowthRate_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:59:51.88553+00:00
-- url     : https://prove2.me/submissions/bcb89065-e160-459b-b08b-ef362776aa90

import Definitions.Def_Eden_GlobalGrowthLimits
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_OrderedStationarySpectrum
import Definitions.Def_Eden_ExactGlobalGrowth
import Theorems.Thm_Eden_globalLogGrowth_five

set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 ≤ c) : globalGrowthRate c 5 = 4 - c := by
  apply Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [globalLogGrowth_five hc ht.le, mul_div_cancel_right₀ _ ht.ne']
end Eden
