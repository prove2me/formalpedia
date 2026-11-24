-- Prove2me | solution 1 for FairSelling.ChargeTPS.req_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:46:08.03892+00:00
-- url     : https://prove2.me/submissions/c1a0b253-5f4d-4593-a098-bb06e0865818

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Theorems.Thm_FairSelling_ChargeTPS_vbarSum_nonneg_of_price
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_GeneralTPS_thr_nonneg
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_bundle
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_cash
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_served
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
namespace FairSelling.ChargeTPS
theorem _root_.solution (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps) {s : CStage G n}
    (hs : s.Good v p eps) (j : Fin n) : 0 ≤ s.req v p eps j := by
  unfold CStage.req
  by_cases hj : j ∈ s.served
  · simp only [if_pos hj]
    have h1 : 0 ≤ vbarSum (v j) p (s.bundle j) := vbarSum_nonneg_of_price p hp _ _
    have h2 : 0 ≤ s.cash j := hs.2.2.2.2.1 j
    linarith
  · simp only [if_neg hj]
    exact GeneralTPS.thr_nonneg v p hn hp j
end FairSelling.ChargeTPS
