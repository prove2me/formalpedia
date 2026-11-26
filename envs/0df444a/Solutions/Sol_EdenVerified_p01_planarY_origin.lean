-- Prove2me | solution 1 for EdenVerified.p01_planarY_origin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:04:06.197404+00:00
-- url     : https://prove2.me/submissions/89f9467d-4e7e-40d6-b4c6-596d4dedec6b

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_planarY_origin
attribute [local simp] Eden.planarY_origin



set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (Ω t : ℝ),
    planarY Ω t 0 0 = 0 :=
  @Eden.planarY_origin
end EdenVerified
