-- Prove2me | solution 1 for FairSelling.PotTPS.QStage.cutSet_subset_sold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:42:02.660778+00:00
-- url     : https://prove2.me/submissions/e1d63788-adb9-4ee5-a027-1fbbd9d54246

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
theorem _root_.solution (s : QStage G n) : s.cutSet ⊆ s.sold := fun _ hg =>
  Finset.mem_union_right _ hg
end FairSelling.PotTPS.QStage
