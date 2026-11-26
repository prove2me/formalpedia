-- Prove2me | solution 1 for Eden.tendsto_globalLogGrowth_div_inf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:03:43.952801+00:00
-- url     : https://prove2.me/submissions/79bb9d73-fced-46fe-b68d-99b4fc84c432

import Definitions.Def_Eden_RealSubadditive
import Definitions.Def_Eden_GlobalGrowthLimits
import Theorems.Thm_Eden_exists_globalLogGrowth_linear_bound
import Theorems.Thm_Eden_globalLogGrowth_subadditive
import Theorems.Thm_Eden_tendsto_real_subadditive_div


set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution {k : ℕ} (hk : k ≤ 5) {c : ℝ}
    (hc : 4 ≤ c) :
    Tendsto (fun t : ℝ => globalLogGrowth c k t / t) atTop
      (𝓝 (sInf ((fun T : ℝ => globalLogGrowth c k T / T) '' Ioi 0))) := by
  obtain ⟨C, hC, hb⟩ := exists_globalLogGrowth_linear_bound hk hc
  exact tendsto_real_subadditive_div
    (fun _ _ hs ht => globalLogGrowth_subadditive hk hc hs ht) hC hb
end Eden
