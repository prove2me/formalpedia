-- Prove2me | solution 1 for EdenVerified.p22_limitingSquaredRadius_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:33:30.579061+00:00
-- url     : https://prove2.me/submissions/cf41fc36-e431-4497-9ed8-318ae13f142d

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_limitingSquaredRadius_eq_one_iff


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (s : ℝ),
    limitingSquaredRadius s = 1 ↔ s = 1 :=
  @Eden.limitingSquaredRadius_eq_one_iff
end EdenVerified
