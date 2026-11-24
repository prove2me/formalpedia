-- Prove2me | solution 1 for FairSelling.PhaseTPS.good_emptyPStage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:59:07.0168+00:00
-- url     : https://prove2.me/submissions/d1508025-f837-4724-ac2a-dc8fb78be71c

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
namespace FairSelling.PhaseTPS
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) :
    (emptyPStage G n).Good v p eps := by
  classical
  have hsold : (emptyPStage G n).sold = (∅ : Finset G) := by
    ext x; simp [PStage.sold, PStage.charge, emptyPStage]
  refine ⟨fun i _ => ⟨rfl, rfl, rfl, rfl, rfl⟩, fun i j _ => by simp [emptyPStage],
    fun i j => by simp [PStage.charge, emptyPStage], fun i j _ => by simp [emptyPStage],
    fun i j => by simp [emptyPStage], fun i g hg => absurd hg (by simp [emptyPStage]),
    fun i i' _ g hg _ => absurd hg (by simp [emptyPStage]),
    fun i => le_rfl, fun i => le_rfl, le_rfl, fun i => by simp [emptyPStage], ?_, ?_, ?_, ?_⟩
  · rw [hsold]; simp [emptyPStage]
  · intro i hi; exact absurd hi (by simp [emptyPStage])
  · intro i hi; exact absurd hi (by simp [emptyPStage])
  · intro i hi; exact absurd hi (by simp [emptyPStage])
end FairSelling.PhaseTPS
