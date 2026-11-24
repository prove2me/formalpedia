-- Prove2me | solution 1 for FairSelling.MixedGood.mixed_Qc_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:58:52.556608+00:00
-- url     : https://prove2.me/submissions/49365ef6-a577-4a9d-922c-42ac3f78ac55

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhaseImp
import Definitions.Def_RequestProject_TPSSefxMixedExample
import Theorems.Thm_FairSelling_MixedGood_mixedThr_pos
import Theorems.Thm_FairSelling_MixedGood_empty_req
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
open FairSelling.MixedGood
namespace FairSelling.MixedGood
theorem _root_.solution (eps : ℝ) :
    0 < CfgTPS.Qc mv mp ((PhaseTPS.emptyPStage (Fin 3) 2).req mv mp eps) 0 (∅ : Finset (Fin 3)) := by
  have hgap : 0 < CfgTPS.gapMin mv mp ((PhaseTPS.emptyPStage (Fin 3) 2).req mv mp eps) 0
      (∅ : Finset (Fin 3)) := by
    change 0 < Finset.univ.inf' Finset.univ_nonempty _
    rw [Finset.lt_inf'_iff]
    intro j _
    rw [empty_req]
    have hv : vbarSum (mv j) mp (∅ : Finset (Fin 3)) = 0 := by simp [vbarSum]
    rw [hv]
    have := mixedThr_pos j
    linarith
  have : CfgTPS.Qc mv mp ((PhaseTPS.emptyPStage (Fin 3) 2).req mv mp eps) 0
      (∅ : Finset (Fin 3)) = max 0 _ := rfl
  rw [this]
  exact lt_of_lt_of_le hgap (le_max_right _ _)
end FairSelling.MixedGood
