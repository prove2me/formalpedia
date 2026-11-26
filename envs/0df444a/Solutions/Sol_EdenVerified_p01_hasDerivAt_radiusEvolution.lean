-- Prove2me | solution 1 for EdenVerified.p01_hasDerivAt_radiusEvolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:04:01.44296+00:00
-- url     : https://prove2.me/submissions/422174ca-1866-43a9-80ca-e65b8f1d7f05

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_hasDerivAt_radiusEvolution


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r),
    HasDerivAt (fun τ => radiusEvolution τ r) (radialField (radiusEvolution t r)) t :=
  @Eden.hasDerivAt_radiusEvolution
end EdenVerified
