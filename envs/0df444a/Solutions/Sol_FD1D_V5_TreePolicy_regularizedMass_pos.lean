-- Prove2me | solution 1 for FD1D.V5.TreePolicy.regularizedMass_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:51:43.355425+00:00
-- url     : https://prove2.me/submissions/37d3d333-9c97-4db6-98a4-6bc99b395fb0

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
import Theorems.Thm_FD1D_nodeMass_pos


set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}
namespace FD1D.V5.TreePolicy
theorem _root_.solution
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (d : ℕ) (v : DyadicNode d) :
    0 < regularizedMass I a d v := by
  unfold regularizedMass intervalMass inventory
  exact div_pos (nodeMass_pos d v) (by positivity)
end FD1D.V5.TreePolicy
