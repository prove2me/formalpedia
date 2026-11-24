-- Prove2me | solution 1 for FairSelling.MixedGood.mixed_not_pure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:52:33.382804+00:00
-- url     : https://prove2.me/submissions/5e4c6cc9-dde7-49c2-9ab4-a7ccab891eef

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhaseImp
import Definitions.Def_RequestProject_TPSSefxMixedExample
import Theorems.Thm_FairSelling_MixedGood_mixedTPS_one_ge
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
theorem _root_.solution (g : Fin 3) : ¬ PhaseTPS.PureGood mv mp (∅ : Finset (Fin 2)) g := by
  intro h
  have h1 := h 1 (by simp)
  have hT := mixedTPS_one_ge
  unfold ChargeTPS.saleLoss trunc at h1
  have hmvpos : 6 ≤ mv 1 g := by fin_cases g <;> norm_num [mv]
  have hmp4 : mp g ≤ 4 := by fin_cases g <;> norm_num [mp]
  have h2 : (6 : ℝ) ≤ min (mv 1 g) (TPS 2 (mv 1) mp) := le_min hmvpos (by linarith)
  have h3 : (6 : ℝ) ≤ max (mp g) (min (mv 1 g) (TPS 2 (mv 1) mp)) :=
    le_trans h2 (le_max_right _ _)
  linarith
end FairSelling.MixedGood
