-- Prove2me | solution 1 for EdenVerified.p21_limiting_rates_of_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:31:51.947179+00:00
-- url     : https://prove2.me/submissions/2efc9d21-e59d-452a-bcc5-328984fcb87a

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_limiting_rates_of_one_lt


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {s : ℝ} (hs : 1 < s),
    radialRate (limitingSquaredRadius s) = -4 ∧
      tangentialRate (limitingSquaredRadius s) = 0 :=
  @Eden.limiting_rates_of_one_lt
end EdenVerified
