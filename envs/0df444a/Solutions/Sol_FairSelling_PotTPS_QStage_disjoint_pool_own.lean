-- Prove2me | solution 1 for FairSelling.PotTPS.QStage.disjoint_pool_own
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:47:40.369959+00:00
-- url     : https://prove2.me/submissions/36c49177-b975-402d-b695-68603c254e1a

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
import Theorems.Thm_FairSelling_PotTPS_QStage_own_subset_sold
import Theorems.Thm_FairSelling_PotTPS_QStage_disjoint_pool_sold

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PotTPS.QStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
namespace FairSelling.PotTPS.QStage
theorem _root_.solution (s : QStage G n) (i : Fin n) : Disjoint s.pool (s.own i) :=
  Finset.disjoint_of_subset_right (own_subset_sold s i) (disjoint_pool_sold s)
end FairSelling.PotTPS.QStage
