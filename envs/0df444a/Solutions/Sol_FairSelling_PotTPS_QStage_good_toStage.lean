-- Prove2me | solution 1 for FairSelling.PotTPS.QStage.good_toStage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:54:34.764002+00:00
-- url     : https://prove2.me/submissions/2d8de0c3-85df-4ad8-849a-d90d2ca33c80

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
import Theorems.Thm_FairSelling_PotTPS_QStage_bank_nonneg
import Theorems.Thm_P2M_FairSelling_PotTPS_QStage_pot_nonneg__175ac3e55641
import Theorems.Thm_FairSelling_PotTPS_QStage_qcounting
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_served
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_bundle
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_cash
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_soldSet
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_GeneralTPS_thr_nonneg
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
open FairSelling.PotTPS.QStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
variable {v p eps}
namespace FairSelling.PotTPS.QStage
theorem _root_.solution (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps) {s : QStage G n}
    (hs : s.Good v p eps) : (s.toStage).Good v p eps := by
  classical
  have hresvsum : 0 ≤ ∑ i, s.resv i := Finset.sum_nonneg (fun i _ => hs.resv_nonneg i)
  have hbank := bank_nonneg hs
  refine ⟨fun i hi => ⟨(hs.unserved i hi).1, (hs.unserved i hi).2.2.2.1⟩, hs.bundle_disj,
    hs.sold_bundle, hs.cash_nonneg, by show (0:ℝ) ≤ s.bank + ∑ i, s.resv i; linarith, ?_,
    hs.share, ?_, ?_⟩
  · show (∑ i, s.cash i) + (s.bank + ∑ i, s.resv i) = ∑ g ∈ s.sold, p g
    have := hs.money; linarith
  · -- safety
    intro i hi j
    have hreq : s.req v p eps j ≤ (s.toStage).guar v p j + eps := by
      unfold req GeneralTPS.Stage.guar
      by_cases hj : j ∈ s.served
      · simp [hj, toStage]
      · simp [hj, toStage]; linarith
    rcases hs.safe i hi j with h | ⟨h1, h2, h3⟩
    · exact Or.inl (le_trans h hreq)
    · exact Or.inr ⟨h1, h2, fun g hg => le_trans (h3 g hg) hreq⟩
  · -- the counting invariant
    intro j hj
    have h := qcounting hn hp hs j hj
    have h2 : 0 ≤ ∑ g ∈ s.cutSet, min (s.pot p g) (GeneralTPS.thr v p j) :=
      Finset.sum_nonneg (fun g _ =>
        le_min (pot_nonneg' hp hs g) (GeneralTPS.thr_nonneg v p hn hp j))
    show (2 * ((n : ℝ) - s.served.card) - 1) * GeneralTPS.thr v p j
      ≤ truncBundle (v j) p (TPS n (v j) p) s.pool + (s.bank + ∑ i, s.resv i)
    linarith
end FairSelling.PotTPS.QStage
