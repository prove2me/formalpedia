-- Prove2me | solution 1 for FairSelling.ChargeTPS.saleLoss_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:56:37.121994+00:00
-- url     : https://prove2.me/submissions/79cb2f65-5aaa-4cdc-ae4b-29ab0b4a72eb

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxGeneral
import Definitions.Def_RequestProject_TPSSefxCharge

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G] [DecidableEq G]
namespace FairSelling.ChargeTPS
theorem _root_.solution (w p : G → ℝ) (t : ℝ) (g : G) : 0 ≤ saleLoss w p t g :=
  sub_nonneg.mpr (le_max_left _ _)
end FairSelling.ChargeTPS
