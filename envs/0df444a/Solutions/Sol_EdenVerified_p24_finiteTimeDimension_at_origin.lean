-- Prove2me | solution 1 for EdenVerified.p24_finiteTimeDimension_at_origin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:16:30.43043+00:00
-- url     : https://prove2.me/submissions/cb8e0599-7223-448a-ae9a-49d7ffaecea4

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_finiteTimeDimension_at_origin


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c t : ℝ} (hc : 4 < c) (ht : 0 < t),
    finiteTimeDimension c t 0 = 0 :=
  @Eden.finiteTimeDimension_at_origin
end EdenVerified
