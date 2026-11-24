-- Prove2me | solution 1 for FairSelling.MixedGood.mixedTPS_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:53:19.692179+00:00
-- url     : https://prove2.me/submissions/1c80f242-9a83-4270-940d-45c830f748db

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhaseImp
import Definitions.Def_RequestProject_TPSSefxMixedExample
import Theorems.Thm_FairSelling_MixedGood_mp_nonneg
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_bank
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_bundle
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_cash
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_resv
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_served
import Theorems.Thm_FairSelling_TPS_le_PS
import Theorems.Thm_FairSelling_le_TPS_of_le_truncSum
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
theorem _root_.solution : TPS 2 (mv 0) mp = 2 := by
  have hPS : PS 2 (mv 0) mp = 2 := by
    unfold PS
    rw [Fin.sum_univ_three]
    simp [mv, mp]
    norm_num
  refine le_antisymm ?_ ?_
  · have := TPS_le_PS (n := 2) (mv 0) mp mp_nonneg
    rw [hPS] at this
    exact this
  · refine le_TPS_of_le_truncSum (mv 0) mp ?_
    unfold truncSum
    rw [Fin.sum_univ_three]
    simp [mv, mp]
    norm_num
end FairSelling.MixedGood
