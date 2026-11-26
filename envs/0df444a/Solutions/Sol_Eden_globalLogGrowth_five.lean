-- Prove2me | solution 1 for Eden.globalLogGrowth_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:58:41.886152+00:00
-- url     : https://prove2.me/submissions/32839363-281e-4cd2-b0af-066a7c35ee69

import Definitions.Def_Eden_GlobalGrowthLimits
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_OrderedStationarySpectrum
import Definitions.Def_Eden_ExactGlobalGrowth
import Theorems.Thm_Eden_supremumSingularProduct_four_five

set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ} (hc : 4 ≤ c) (ht : 0 ≤ t) :
    globalLogGrowth c 5 t = (4 - c) * t := by
  rw [globalLogGrowth, supremumSingularProduct_four_five hc ht (by norm_num) (by norm_num),
    Real.log_exp]
  norm_num
  ring
end Eden
