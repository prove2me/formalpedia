-- Prove2me | solution 1 for FairSelling.ChargeTPS.cost_le_of_single_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:44:24.603577+00:00
-- url     : https://prove2.me/submissions/9462407c-7a6b-4513-aef3-04cc27d40cd5

import Mathlib
import Definitions.Def_RequestProject_TPSSefxCharge
import Definitions.Def_RequestProject_TPSSefxServe
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_ChargeTPS_cash_add_saleLoss_le
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_bundle
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_cash
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_served
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G] [DecidableEq G]
namespace FairSelling.ChargeTPS
theorem _root_.solution (w p : G → ℝ) (t : ℝ) (g : G) (q : ℝ) (hqp : q ≤ p g) (hqt : q ≤ t) :
    truncBundle w p t ∅ + q + 0 + ∑ x ∈ ({g} : Finset G), saleLoss w p t x ≤ t := by
  simp only [truncBundle, Finset.sum_empty, Finset.sum_singleton, zero_add, add_zero]
  exact cash_add_saleLoss_le w p t g q hqp hqt
end FairSelling.ChargeTPS
