-- Prove2me | solution 1 for Eden.globalGrowthRate_eq_inf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:04:57.994481+00:00
-- url     : https://prove2.me/submissions/e289c596-c5ee-4b8f-9886-3c4d10f967b7

import Definitions.Def_Eden_RealSubadditive
import Definitions.Def_Eden_GlobalGrowthLimits
import Theorems.Thm_Eden_tendsto_globalLogGrowth_div_inf

set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution {k : ℕ} (hk : k ≤ 5) {c : ℝ} (hc : 4 ≤ c) :
    globalGrowthRate c k =
      sInf ((fun T : ℝ => globalLogGrowth c k T / T) '' Ioi 0) :=
  (tendsto_globalLogGrowth_div_inf hk hc).limUnder_eq
end Eden
