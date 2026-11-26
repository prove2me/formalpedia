-- Prove2me | solution 1 for EdenVerified.p03_radiusEvolution_at_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:08:32.968795+00:00
-- url     : https://prove2.me/submissions/02aca88c-6879-4cf3-b786-a228d2bcdcc2

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_radiusEvolution_at_one
attribute [local simp] Eden.radiusEvolution_at_one



set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (t : ℝ),
    radiusEvolution t 1 = 1 :=
  @Eden.radiusEvolution_at_one
end EdenVerified
