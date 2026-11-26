-- Prove2me | solution 1 for EdenVerified.p22_limitingSquaredRadius_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:33:28.820933+00:00
-- url     : https://prove2.me/submissions/cd9228a6-259b-489f-b1d9-d9d410d54eef

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_limitingSquaredRadius_cases


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (s : ℝ),
    limitingSquaredRadius s = 0 ∨ limitingSquaredRadius s = 1 ∨ limitingSquaredRadius s = 2 :=
  @Eden.limitingSquaredRadius_cases
end EdenVerified
