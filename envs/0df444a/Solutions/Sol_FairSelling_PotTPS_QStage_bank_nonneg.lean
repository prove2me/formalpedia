-- Prove2me | solution 1 for FairSelling.PotTPS.QStage.bank_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:48:03.690813+00:00
-- url     : https://prove2.me/submissions/8b49f11e-38cd-4efb-b0a7-fc465eeb7bd6

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
theorem _root_.solution {s : QStage G n} (hs : s.Good v p eps) : 0 ≤ s.bank := by
  have h1 : 0 ≤ ∑ g ∈ s.cutSet, s.pot p g :=
    Finset.sum_nonneg (fun g hg => hs.pot_nonneg g hg)
  linarith [hs.bank_pot]
end FairSelling.PotTPS.QStage
