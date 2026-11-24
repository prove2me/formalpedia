-- Prove2me | solution 1 for FairSelling.PotTPS.QStage.pot_of_pool
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:51:08.833751+00:00
-- url     : https://prove2.me/submissions/1aa5d9aa-3d43-4118-80e5-ba1315bf9d6c

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
import Theorems.Thm_FairSelling_PotTPS_QStage_disjoint_pool_src
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
variable {v p eps}
namespace FairSelling.PotTPS.QStage
theorem _root_.solution {s : QStage G n} {g : G} (hg : g ∈ s.pool) : s.pot p g = p g := by
  have hh : s.holders g = ∅ := by
    refine Finset.eq_empty_of_forall_notMem (fun i hi => ?_)
    simp only [holders, Finset.mem_filter] at hi
    exact Finset.disjoint_left.mp (disjoint_pool_src s i) hg hi.2
  simp [pot, hh]
end FairSelling.PotTPS.QStage
