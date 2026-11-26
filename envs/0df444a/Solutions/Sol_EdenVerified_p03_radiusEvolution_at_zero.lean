-- Prove2me | solution 1 for EdenVerified.p03_radiusEvolution_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:08:15.162608+00:00
-- url     : https://prove2.me/submissions/526418e7-62bf-4d79-8b70-b3684c0a94d0

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_radiusEvolution_at_zero
attribute [local simp] Eden.radiusEvolution_at_zero



set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (t : ℝ),
    radiusEvolution t 0 = 0 :=
  @Eden.radiusEvolution_at_zero
end EdenVerified
