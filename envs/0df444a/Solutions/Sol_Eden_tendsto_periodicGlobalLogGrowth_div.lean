-- Prove2me | solution 1 for Eden.tendsto_periodicGlobalLogGrowth_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:21:47.991107+00:00
-- url     : https://prove2.me/submissions/5fab6748-5cd2-466d-99b3-8b401e944bc3

import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_ExteriorCocycle
import Definitions.Def_Eden_PeriodicGlobalGrowth
import Theorems.Thm_Eden_periodicGlobalLogGrowth_eq

set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c)
    {k : ℕ} (hk : k ≤ 5) :
    Tendsto (fun t : ℝ => periodicGlobalLogGrowth c k t / t) atTop
      (𝓝 (spectrumPartialSum ![2, 0, -2, -2, -c] k)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [periodicGlobalLogGrowth_eq hc ht.le hk, mul_div_cancel_left₀ _ ht.ne']
end Eden
