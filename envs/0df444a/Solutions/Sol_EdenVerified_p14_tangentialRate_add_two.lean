-- Prove2me | solution 1 for EdenVerified.p14_tangentialRate_add_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:25:06.438799+00:00
-- url     : https://prove2.me/submissions/b02ec805-8567-4b16-96ba-e2518260b98b

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_tangentialRate_add_two


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (s : ℝ),
    tangentialRate s + 2 = s * (3 - s) :=
  @Eden.tangentialRate_add_two
end EdenVerified
