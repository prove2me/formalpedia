-- Prove2me | solution 1 for FairSelling.PotTPS.QStage.own_subset_sold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:00:57.341789+00:00
-- url     : https://prove2.me/submissions/faecb7db-b204-47ac-b6a2-2a4f7fd08695

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
omit [Fintype G]
namespace FairSelling.PotTPS.QStage
theorem _root_.solution (s : QStage G n) (i : Fin n) : s.own i ⊆ s.sold :=
  fun _ hg => Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hg⟩)
end FairSelling.PotTPS.QStage
