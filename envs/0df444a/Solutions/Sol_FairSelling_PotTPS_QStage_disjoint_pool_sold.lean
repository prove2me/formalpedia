-- Prove2me | solution 1 for FairSelling.PotTPS.QStage.disjoint_pool_sold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:32:02.038604+00:00
-- url     : https://prove2.me/submissions/7b0649af-e875-4ef2-9013-b5845cb9d378

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
theorem _root_.solution (s : QStage G n) : Disjoint s.pool s.sold := by
  refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
  simp only [pool, Finset.mem_sdiff, Finset.mem_union] at hx
  exact hx.2 (Or.inl hx')
end FairSelling.PotTPS.QStage
