-- Prove2me | solution 1 for Eden.globalGrowthRate_five_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:01:43.207447+00:00
-- url     : https://prove2.me/submissions/7ccddeb9-0ad5-4e4b-89c3-15c5c145a9b7

import Definitions.Def_Eden_GlobalGrowthLimits
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_OrderedStationarySpectrum
import Definitions.Def_Eden_ExactGlobalGrowth
import Theorems.Thm_Eden_globalGrowthRate_five

set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) : globalGrowthRate c 5 < 0 := by
  rw [globalGrowthRate_five hc.le]
  linarith
end Eden
