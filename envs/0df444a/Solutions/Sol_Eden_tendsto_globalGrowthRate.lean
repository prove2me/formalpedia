-- Prove2me | solution 1 for Eden.tendsto_globalGrowthRate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:09:24.941183+00:00
-- url     : https://prove2.me/submissions/a8a5a0a8-1a34-4bd2-9c09-af367d21d399

import Definitions.Def_Eden_RealSubadditive
import Definitions.Def_Eden_GlobalGrowthLimits
import Theorems.Thm_Eden_tendsto_globalLogGrowth_div_inf
import Theorems.Thm_Eden_globalGrowthRate_eq_inf

set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution {k : ℕ} (hk : k ≤ 5) {c : ℝ} (hc : 4 ≤ c) :
    Tendsto (fun t : ℝ => globalLogGrowth c k t / t) atTop
      (𝓝 (globalGrowthRate c k)) := by
  rw [globalGrowthRate_eq_inf hk hc]
  exact tendsto_globalLogGrowth_div_inf hk hc
end Eden
