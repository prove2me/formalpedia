-- Prove2me | solution 1 for FairSelling.ChargeTPS.sum_saleLoss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:23:51.178002+00:00
-- url     : https://prove2.me/submissions/02b81c43-8148-49a6-ba7b-e011734f1431

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
theorem _root_.solution (w p : G → ℝ) (t : ℝ) (X : Finset G) :
    ∑ g ∈ X, saleLoss w p t g = truncBundle w p t X - ∑ g ∈ X, p g := by
  unfold saleLoss truncBundle
  rw [Finset.sum_sub_distrib]
end FairSelling.ChargeTPS
