-- Prove2me | solution 1 for FairSelling.PotTPS.good_emptyQStage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:50:58.558515+00:00
-- url     : https://prove2.me/submissions/7a80689e-b10c-429a-af04-545346101021

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_served
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_bundle
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_cash
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_soldSet
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_bundle
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_cash
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_served
attribute [local simp] FairSelling.restrictVal_mem


attribute [local simp] FairSelling.PotTPS.QStage.toStage_served
attribute [local simp] FairSelling.PotTPS.QStage.toStage_bundle
attribute [local simp] FairSelling.PotTPS.QStage.toStage_cash
attribute [local simp] FairSelling.PotTPS.QStage.toStage_soldSet

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling.PotTPS
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) :
    (emptyQStage G n).Good v p eps := by
  classical
  have hcut : (emptyQStage G n).cutSet = (∅ : Finset G) := by
    ext x; simp [QStage.cutSet, emptyQStage]
  have hsold : (emptyQStage G n).sold = (∅ : Finset G) := by
    ext x; simp [QStage.sold, QStage.cutSet, emptyQStage]
  refine ⟨fun i _ => ⟨rfl, rfl, rfl, rfl, rfl⟩, fun i j _ => by simp [emptyQStage],
    fun i => by simp [hsold], fun i j _ => by simp [emptyQStage],
    fun i j => by simp [emptyQStage], fun i => by simp [emptyQStage],
    fun i hi => absurd (rfl : (emptyQStage G n).src i = ∅) hi,
    fun i => le_rfl, fun i => le_rfl, ?_, ?_, fun i => by simp [emptyQStage], ?_, ?_, ?_, ?_,
    fun i hi => absurd (rfl : (emptyQStage G n).src i = ∅) hi⟩
  · intro g hg; rw [hcut] at hg; exact absurd hg (by simp)
  · rw [hcut]; simp [emptyQStage]
  · rw [hsold]; simp [emptyQStage]
  · intro i hi; exact absurd hi (by simp [emptyQStage])
  · intro i hi; exact absurd hi (by simp [emptyQStage])
  · intro i hi; exact absurd hi (by simp [emptyQStage])
end FairSelling.PotTPS
