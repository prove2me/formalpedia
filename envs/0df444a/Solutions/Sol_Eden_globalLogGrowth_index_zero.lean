-- Prove2me | solution 1 for Eden.globalLogGrowth_index_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:01:17.341735+00:00
-- url     : https://prove2.me/submissions/2020b784-5b21-4ef8-8459-856f94b75856

import Definitions.Def_Eden_GlobalGrowthLimits
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_OrderedStationarySpectrum
import Definitions.Def_Eden_ExactGlobalGrowth
import Theorems.Thm_Eden_globalLogGrowth_bounds


set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ} (hc : 4 ≤ c) (ht : 0 ≤ t) :
    globalLogGrowth c 0 t = 0 := by
  have hb := globalLogGrowth_bounds (k := 0) (by omega) hc ht
  norm_num at hb
  exact le_antisymm hb.2 hb.1
end Eden
