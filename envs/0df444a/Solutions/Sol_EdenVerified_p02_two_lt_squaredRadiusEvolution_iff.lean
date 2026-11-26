-- Prove2me | solution 1 for EdenVerified.p02_two_lt_squaredRadiusEvolution_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:06:50.983402+00:00
-- url     : https://prove2.me/submissions/a102e14a-c23c-46b4-b02d-0b01b4e0c834

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_two_lt_squaredRadiusEvolution_iff


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {t s : ℝ} (ht : 0 ≤ t),
    2 < squaredRadiusEvolution t s ↔ 2 < s :=
  @Eden.two_lt_squaredRadiusEvolution_iff
end EdenVerified
