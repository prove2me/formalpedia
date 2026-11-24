-- Prove2me | solution 1 for FairSelling.PotTPS.QStage.disjoint_pool_bundle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:47:30.433843+00:00
-- url     : https://prove2.me/submissions/68917823-b00f-471c-a9d2-c75f73f3a565

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
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
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PotTPS.QStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
namespace FairSelling.PotTPS.QStage
theorem _root_.solution (s : QStage G n) (i : Fin n) : Disjoint s.pool (s.bundle i) := by
  refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
  simp only [pool, Finset.mem_sdiff, Finset.mem_union] at hx
  exact hx.2 (Or.inr (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx'⟩))
end FairSelling.PotTPS.QStage
