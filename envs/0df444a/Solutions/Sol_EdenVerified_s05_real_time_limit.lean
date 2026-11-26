-- Prove2me | solution 1 for EdenVerified.s05_real_time_limit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:57:31.632666+00:00
-- url     : https://prove2.me/submissions/81292dd2-d1b3-49a7-be97-38a5c1a7f7ea

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_globalGrowthRate_eq_inf
import Theorems.Thm_Eden_tendsto_globalGrowthRate


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (hc : 4 < c) (k : ℕ) (hk : k ≤ 5) :
    Tendsto (fun t : ℝ => globalLogGrowth c k t / t) atTop
      (𝓝 (globalGrowthRate c k)) ∧
    globalGrowthRate c k = sInf ((fun T : ℝ => globalLogGrowth c k T / T) '' Ioi 0) :=
  ⟨tendsto_globalGrowthRate hk hc.le, globalGrowthRate_eq_inf hk hc.le⟩
end EdenVerified
