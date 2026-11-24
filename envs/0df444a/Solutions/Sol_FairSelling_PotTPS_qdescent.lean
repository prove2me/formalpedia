-- Prove2me | solution 1 for FairSelling.PotTPS.qdescent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:59:36.3223+00:00
-- url     : https://prove2.me/submissions/479dd9ad-5436-4152-85fb-d0be99b5c5b6

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_served
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_bundle
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_cash
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_soldSet
import Theorems.Thm_FairSelling_PotTPS_qtotal_nonneg
import Theorems.Thm_FairSelling_PotTPS_qdescent_inner
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
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
namespace FairSelling.PotTPS
theorem _root_.solution (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 < eps)
    (hstep : QImprovementStep v p eps) :
    ∀ (c : ℕ) (s : QStage G n), s.Good v p eps → n - s.served.card ≤ c →
      ∃ s' : QStage G n, s'.Good v p eps ∧ s'.served = Finset.univ := by
  intro c
  induction c with
  | zero =>
    intro s hs hc
    refine ⟨s, hs, ?_⟩
    have h1 : s.served.card ≤ n := by
      simpa using Finset.card_le_card (Finset.subset_univ s.served)
    have : s.served.card = n := by omega
    exact Finset.eq_univ_of_card _ (by simpa using this)
  | succ c ihc =>
    intro s hs hc
    obtain ⟨b, hbb⟩ : ∃ b : ℕ, GeneralTPS.totalBound v p ≤ (b : ℝ) * eps := by
      obtain ⟨b, hb⟩ := exists_nat_gt (GeneralTPS.totalBound v p / eps)
      exact ⟨b, by rw [div_lt_iff₀ heps] at hb; linarith⟩
    refine qdescent_inner v p eps hn hp heps hstep c ihc b s hs hc ?_
    have := qtotal_nonneg v p eps hn hp heps.le hs
    linarith
end FairSelling.PotTPS
