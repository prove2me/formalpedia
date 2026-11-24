-- Prove2me | solution 1 for FairSelling.MixedGood.mixed_case_reached
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:46:16.383834+00:00
-- url     : https://prove2.me/submissions/581d7785-1671-4ca0-b580-1cdb6631f59d

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhaseImp
import Definitions.Def_RequestProject_TPSSefxMixedExample
import Theorems.Thm_FairSelling_MixedGood_mixed_expensive
import Theorems.Thm_FairSelling_MixedGood_mixed_not_pure
import Theorems.Thm_FairSelling_MixedGood_empty_pool
import Theorems.Thm_FairSelling_MixedGood_empty_served
import Theorems.Thm_FairSelling_MixedGood_empty_bank
import Theorems.Thm_FairSelling_MixedGood_mixed_Qc_pos
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_bank
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_bundle
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_cash
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_resv
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_served
import Theorems.Thm_FairSelling_PhaseTPS_good_emptyPStage
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
    (PhaseTPS.emptyPStage (Fin 3) 2).Good mv mp eps ∧
    (0 : Fin 2) ∉ (PhaseTPS.emptyPStage (Fin 3) 2).served ∧
    (0 : Fin 3) ∈ (PhaseTPS.emptyPStage (Fin 3) 2).pool ∧
    2 * GeneralTPS.thr mv mp 0 < mp 0 ∧
    ¬ PhaseTPS.PureGood mv mp (PhaseTPS.emptyPStage (Fin 3) 2).served 0 ∧
    (∀ F : Finset (Fin 3), F ⊆ (PhaseTPS.emptyPStage (Fin 3) 2).pool →
      (∀ x ∈ F, PhaseTPS.PureGood mv mp (PhaseTPS.emptyPStage (Fin 3) 2).served x) →
      (PhaseTPS.emptyPStage (Fin 3) 2).bank + ∑ x ∈ F, mp x
        < CfgTPS.Qc mv mp ((PhaseTPS.emptyPStage (Fin 3) 2).req mv mp eps) 0
            (∅ : Finset (Fin 3))) := by
  refine ⟨PhaseTPS.good_emptyPStage mv mp eps, by simp [empty_served], ?_,
    mixed_expensive, ?_, ?_⟩
  · rw [empty_pool]; exact Finset.mem_univ _
  · rw [empty_served]; exact mixed_not_pure 0
  · intro F _ hFpure
    have hFempty : F = ∅ := by
      refine Finset.eq_empty_of_forall_notMem (fun x hx => ?_)
      have := hFpure x hx
      rw [empty_served] at this
      exact mixed_not_pure x this
    rw [hFempty, empty_bank]
    simpa using mixed_Qc_pos eps
end FairSelling.MixedGood
