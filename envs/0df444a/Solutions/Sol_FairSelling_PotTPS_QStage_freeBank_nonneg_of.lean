-- Prove2me | solution 1 for FairSelling.PotTPS.QStage.freeBank_nonneg_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:42:18.913828+00:00
-- url     : https://prove2.me/submissions/14955b19-3ba4-4d08-988c-ef891d031b5c

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
theorem _root_.solution {s : QStage G n} (hs : s.Good v p eps) : 0 ≤ s.freeBank p := by
  have := hs.bank_pot
  unfold freeBank
  linarith
end FairSelling.PotTPS.QStage
