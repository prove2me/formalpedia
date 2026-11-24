-- Prove2me | solution 1 for FairSelling.PotTPS.QStage.cash_add_pot_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:49:02.51842+00:00
-- url     : https://prove2.me/submissions/514da0a8-13e9-4806-a1b2-fe191ab3ad51

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
import Theorems.Thm_P2M_FairSelling_PotTPS_QStage_cash_add_pot_le__f562961c4ebe

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
theorem _root_.solution {s : QStage G n} (hs : s.Good v p eps) {i : Fin n} {g : G}
    (hg : g ∈ s.src i) : s.cash i + s.pot p g ≤ p g :=
  cash_add_pot_le' hs.cash_nonneg hg
end FairSelling.PotTPS.QStage
