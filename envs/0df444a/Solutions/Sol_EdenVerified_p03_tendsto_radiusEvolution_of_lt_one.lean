-- Prove2me | solution 1 for EdenVerified.p03_tendsto_radiusEvolution_of_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:08:39.171908+00:00
-- url     : https://prove2.me/submissions/111dc84a-f470-4ce1-a105-0cc490c220b0

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_tendsto_radiusEvolution_of_lt_one


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {r : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1),
    Tendsto (fun t => radiusEvolution t r) atTop (𝓝 0) :=
  @Eden.tendsto_radiusEvolution_of_lt_one
end EdenVerified
