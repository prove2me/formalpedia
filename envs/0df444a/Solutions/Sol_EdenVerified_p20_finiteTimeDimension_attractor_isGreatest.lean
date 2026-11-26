-- Prove2me | solution 1 for EdenVerified.p20_finiteTimeDimension_attractor_isGreatest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:30:08.315925+00:00
-- url     : https://prove2.me/submissions/6443ba4c-679f-440f-9326-4e1ed510d6be

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_finiteTimeDimension_attractor_isGreatest


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c t : ℝ} (hc : 4 < c) (ht : 0 < t),
    IsGreatest (finiteTimeDimension c t '' attractor) (targetDimension c) :=
  @Eden.finiteTimeDimension_attractor_isGreatest
end EdenVerified
