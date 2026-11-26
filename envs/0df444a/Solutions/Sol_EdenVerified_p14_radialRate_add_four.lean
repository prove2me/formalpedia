-- Prove2me | solution 1 for EdenVerified.p14_radialRate_add_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:25:03.123521+00:00
-- url     : https://prove2.me/submissions/8be2d0e6-521f-4c90-a8fc-61ad26dce290

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_radialRate_add_four


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (s : ℝ),
    radialRate s + 4 = (2 - s) * (5 * s + 1) :=
  @Eden.radialRate_add_four
end EdenVerified
