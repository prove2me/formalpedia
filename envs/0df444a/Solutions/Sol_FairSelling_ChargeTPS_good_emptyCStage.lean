-- Prove2me | solution 1 for FairSelling.ChargeTPS.good_emptyCStage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:42:54.290193+00:00
-- url     : https://prove2.me/submissions/3abed286-bea1-4d56-ab3c-d93c3725e54d

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxGeneral
import Definitions.Def_RequestProject_TPSSefxCharge
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem


attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_served
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_bundle
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_cash

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling.ChargeTPS
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) :
    (emptyCStage G n).Good v p eps := by
  refine ⟨fun i _ => ⟨rfl, rfl, rfl, rfl⟩, fun i j _ => by simp [emptyCStage],
    fun i j _ => by simp [emptyCStage], fun i j => by simp [emptyCStage],
    fun i => le_rfl, fun i => le_rfl, le_rfl, ?_, ?_, ?_, ?_⟩
  · have h : (Finset.univ.biUnion fun _ : Fin n => (∅ : Finset G)) = ∅ := by ext x; simp
    simp [emptyCStage, CStage.soldSet, h]
  · intro i hi; exact absurd hi (by simp [emptyCStage])
  · intro i hi; exact absurd hi (by simp [emptyCStage])
  · intro i hi; exact absurd hi (by simp [emptyCStage])
end FairSelling.ChargeTPS
