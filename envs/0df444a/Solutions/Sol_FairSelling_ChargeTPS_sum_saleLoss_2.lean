-- Prove2me | solution 2 for FairSelling.ChargeTPS.sum_saleLoss
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T01:25:05.433642+00:00
-- url     : https://prove2.me/submissions/caecbd1b-b596-491f-8580-2f29fab38582

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


theorem solution (w p : G → ℝ) (t : ℝ) (X : Finset G) :
    ∑ g ∈ X, saleLoss w p t g = truncBundle w p t X - ∑ g ∈ X, p g := by
  simp [saleLoss,truncBundle,Finset.sum_sub_distrib]
