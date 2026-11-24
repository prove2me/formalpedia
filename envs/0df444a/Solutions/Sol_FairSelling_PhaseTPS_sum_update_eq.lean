-- Prove2me | solution 1 for FairSelling.PhaseTPS.sum_update_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:46:34.334778+00:00
-- url     : https://prove2.me/submissions/e571c7b4-0a84-4855-abf0-c5e9906fc48f

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhase
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPhaseStep
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_bank
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_bundle
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_cash
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_resv
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_served
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_bundle
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_cash
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_served
attribute [local simp] FairSelling.PhaseTPS.PStage.toCStage_bank
attribute [local simp] FairSelling.PhaseTPS.PStage.toCStage_bundle
attribute [local simp] FairSelling.PhaseTPS.PStage.toCStage_cash
attribute [local simp] FairSelling.PhaseTPS.PStage.toCStage_resv
attribute [local simp] FairSelling.PhaseTPS.PStage.toCStage_served
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling.PhaseTPS
theorem _root_.solution {n : ℕ} (f : Fin n → ℝ) (k : Fin n) (a : ℝ) :
    ∑ i, Function.update f k a i = ∑ i, f i - f k + a := by
  classical
  rw [Finset.sum_update_of_mem (Finset.mem_univ k)]
  have h : ∑ x ∈ Finset.univ \ {k}, f x = ∑ x, f x - f k := by
    rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ {k})]
    simp
  rw [h]; ring
end FairSelling.PhaseTPS
