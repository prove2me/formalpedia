-- Prove2me | solution 1 for EdenVerified.p03_tendsto_radiusEvolution_of_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:08:51.921372+00:00
-- url     : https://prove2.me/submissions/db22b958-7d97-4c64-84ef-5d36a3f1fb93

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_tendsto_radiusEvolution_of_one_lt


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {r : ℝ} (hr : 1 < r),
    Tendsto (fun t => radiusEvolution t r) atTop (𝓝 (Real.sqrt 2)) :=
  @Eden.tendsto_radiusEvolution_of_one_lt
end EdenVerified
