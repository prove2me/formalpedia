-- Prove2me | solution 1 for EdenVerified.p21_limiting_rates_at_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:31:42.362794+00:00
-- url     : https://prove2.me/submissions/50609782-60ee-4743-bc7b-d38e549e2809

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_limiting_rates_at_one


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    radialRate (limitingSquaredRadius 1) = 2 ∧
      tangentialRate (limitingSquaredRadius 1) = 0 :=
  @Eden.limiting_rates_at_one
end EdenVerified
