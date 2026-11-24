-- Prove2me | solution 1 for FairSelling.PotTPS.QStage.disjoint_pool_cutSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:47:56.422122+00:00
-- url     : https://prove2.me/submissions/5c066bdf-d49d-42e2-9fef-9f241d3c327f

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
import Theorems.Thm_FairSelling_PotTPS_QStage_cutSet_subset_sold
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
theorem _root_.solution (s : QStage G n) : Disjoint s.pool s.cutSet :=
  Finset.disjoint_of_subset_right (cutSet_subset_sold s) (disjoint_pool_sold s)
end FairSelling.PotTPS.QStage
