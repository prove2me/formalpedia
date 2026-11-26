-- Prove2me | solution 1 for EdenVerified.p21_limiting_rates_of_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:31:22.259004+00:00
-- url     : https://prove2.me/submissions/9b62b423-08dc-4753-b8b6-a8c6758cea30

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_limiting_rates_of_lt_one


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {s : ℝ} (hs : s < 1),
    radialRate (limitingSquaredRadius s) = -2 ∧
      tangentialRate (limitingSquaredRadius s) = -2 :=
  @Eden.limiting_rates_of_lt_one
end EdenVerified
