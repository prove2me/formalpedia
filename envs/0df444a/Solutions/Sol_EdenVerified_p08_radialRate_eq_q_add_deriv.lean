-- Prove2me | solution 1 for EdenVerified.p08_radialRate_eq_q_add_deriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:12:57.974728+00:00
-- url     : https://prove2.me/submissions/ef3f2c6a-a67d-47e3-8b76-9cf1694d4a77

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_radialRate_eq_q_add_deriv


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (s : ℝ),
    radialRate s = q s + 2 * s * deriv q s :=
  @Eden.radialRate_eq_q_add_deriv
end EdenVerified
