-- Prove2me | solution 1 for FairSelling.ChargeTPS.CStage.disjoint_pool_soldSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:57:55.786797+00:00
-- url     : https://prove2.me/submissions/f78fdcb3-c6b1-4aa3-809e-a76752375503

import Mathlib
import Definitions.Def_RequestProject_TPSSefxCharge
import Definitions.Def_RequestProject_TPSSefxServe
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
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
open FairSelling.ChargeTPS.CStage
namespace FairSelling.ChargeTPS.CStage
theorem _root_.solution (s : CStage G n) : Disjoint s.pool s.soldSet := by
  refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
  simp only [CStage.pool, Finset.mem_sdiff, Finset.mem_union] at hx
  exact hx.2 (Or.inl hx')
end FairSelling.ChargeTPS.CStage
