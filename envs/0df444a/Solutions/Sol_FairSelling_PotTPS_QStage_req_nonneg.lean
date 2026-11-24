-- Prove2me | solution 1 for FairSelling.PotTPS.QStage.req_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:48:24.863818+00:00
-- url     : https://prove2.me/submissions/59b513aa-c881-4730-ab32-f738abd2a735

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
import Theorems.Thm_FairSelling_GeneralTPS_thr_nonneg


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
    (hs : s.Good v p eps) (j : Fin n) : 0 ≤ s.req v p eps j := by
  unfold req
  by_cases hj : j ∈ s.served
  · rw [if_pos hj]
    have h1 : 0 ≤ vbarSum (v j) p (s.bundle j) :=
      Finset.sum_nonneg (fun g _ => le_trans (hp g) (le_max_left _ _))
    have h2 := hs.cash_nonneg j
    linarith
  · rw [if_neg hj]
    exact GeneralTPS.thr_nonneg v p hn hp j
end FairSelling.PotTPS.QStage
