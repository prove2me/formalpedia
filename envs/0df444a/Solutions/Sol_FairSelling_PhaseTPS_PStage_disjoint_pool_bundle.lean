-- Prove2me | solution 1 for FairSelling.PhaseTPS.PStage.disjoint_pool_bundle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:46:12.880941+00:00
-- url     : https://prove2.me/submissions/9043d84d-684d-4bed-b816-f3825cc732f3

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxPhase
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_served
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_bundle
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_cash
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_resv
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_bank
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_bundle
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_cash
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_served
attribute [local simp] FairSelling.restrictVal_mem


attribute [local simp] FairSelling.PhaseTPS.PStage.toCStage_served
attribute [local simp] FairSelling.PhaseTPS.PStage.toCStage_bundle
attribute [local simp] FairSelling.PhaseTPS.PStage.toCStage_cash
attribute [local simp] FairSelling.PhaseTPS.PStage.toCStage_resv
attribute [local simp] FairSelling.PhaseTPS.PStage.toCStage_bank

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PhaseTPS.PStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
namespace FairSelling.PhaseTPS.PStage
theorem _root_.solution (s : PStage G n) (i : Fin n) : Disjoint s.pool (s.bundle i) := by
  refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
  simp only [PStage.pool, Finset.mem_sdiff, Finset.mem_union] at hx
  exact hx.2 (Or.inr (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx'⟩))
end FairSelling.PhaseTPS.PStage
