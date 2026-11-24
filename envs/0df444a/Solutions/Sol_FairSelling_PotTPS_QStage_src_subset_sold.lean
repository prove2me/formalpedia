-- Prove2me | solution 1 for FairSelling.PotTPS.QStage.src_subset_sold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:47:14.462449+00:00
-- url     : https://prove2.me/submissions/093de57b-6141-4927-b88e-ce2fd9cf75fb

import Mathlib
import Definitions.Def_RequestProject_TPSSefxConfig
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPot
import Theorems.Thm_FairSelling_PotTPS_QStage_mem_cutSet
import Theorems.Thm_FairSelling_PotTPS_QStage_cutSet_subset_sold

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.PotTPS.QStage
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
omit [Fintype G]
namespace FairSelling.PotTPS.QStage
theorem _root_.solution (s : QStage G n) (i : Fin n) : s.src i ⊆ s.sold :=
  fun _ hg => cutSet_subset_sold s (mem_cutSet hg)
end FairSelling.PotTPS.QStage
