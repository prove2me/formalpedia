-- Prove2me | solution 1 for EdenVerified.p08_tangentialRate_eq_q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:13:26.862151+00:00
-- url     : https://prove2.me/submissions/b9f3f3a2-3684-4b85-8326-a5556b3f79c8

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_tangentialRate_eq_q


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (s : ℝ),
    tangentialRate s = q s :=
  @Eden.tangentialRate_eq_q
end EdenVerified
