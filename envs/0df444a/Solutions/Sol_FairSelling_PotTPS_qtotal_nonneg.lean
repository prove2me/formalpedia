-- Prove2me | solution 1 for FairSelling.PotTPS.qtotal_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:56:15.828246+00:00
-- url     : https://prove2.me/submissions/99e6317d-f3ff-490d-930f-90683fbcd332

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
import Theorems.Thm_FairSelling_PotTPS_QStage_good_toStage
import Theorems.Thm_FairSelling_ChargeTPS_good_toStage
import Theorems.Thm_FairSelling_GeneralTPS_total_nonneg


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
namespace FairSelling.PotTPS
theorem _root_.solution (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps) {s : QStage G n}
    (hs : s.Good v p eps) : 0 ≤ s.total v p :=
  GeneralTPS.total_nonneg v p eps hp (QStage.good_toStage hn hp heps hs)
end FairSelling.PotTPS
