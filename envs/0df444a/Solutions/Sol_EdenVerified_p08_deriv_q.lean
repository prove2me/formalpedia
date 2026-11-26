-- Prove2me | solution 1 for EdenVerified.p08_deriv_q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:12:57.212685+00:00
-- url     : https://prove2.me/submissions/40fe6bdc-679d-4316-9b57-6162aceeaba6

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_deriv_q


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (s : ℝ),
    deriv q s = -2 * s + 3 :=
  @Eden.deriv_q
end EdenVerified
