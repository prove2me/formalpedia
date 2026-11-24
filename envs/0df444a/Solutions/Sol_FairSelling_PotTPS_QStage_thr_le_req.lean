-- Prove2me | solution 1 for FairSelling.PotTPS.QStage.thr_le_req
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:49:08.275094+00:00
-- url     : https://prove2.me/submissions/7d1638e0-c463-4812-8b63-048a3be343fb

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot

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
theorem _root_.solution (heps : 0 ≤ eps) {s : QStage G n} (hs : s.Good v p eps) (j : Fin n) :
    GeneralTPS.thr v p j ≤ s.req v p eps j := by
  unfold req
  by_cases hj : j ∈ s.served
  · rw [if_pos hj]; have := hs.share j hj; linarith
  · rw [if_neg hj]
end FairSelling.PotTPS.QStage
