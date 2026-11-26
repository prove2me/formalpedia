-- Prove2me | solution 1 for EdenVerified.p03_tendsto_radiusEvolution_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:09:12.200034+00:00
-- url     : https://prove2.me/submissions/cc8f764c-98bd-4d56-891a-6a9743e6a8e3

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_tendsto_radiusEvolution_one_iff


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {r : ℝ} (hr : 0 ≤ r),
    Tendsto (fun t => radiusEvolution t r) atTop (𝓝 1) ↔ r = 1 :=
  @Eden.tendsto_radiusEvolution_one_iff
end EdenVerified
