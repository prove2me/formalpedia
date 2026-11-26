-- Prove2me | solution 1 for FD1D.V5.TreePolicy.restoringDrift_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:52:14.041028+00:00
-- url     : https://prove2.me/submissions/4a45fff3-962e-4e99-b8fe-258d5ee79bef

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}
namespace FD1D.V5.TreePolicy
theorem _root_.solution
    (I : AggregatedInventory L m) {a : ℝ} (ha : 0 < a) :
    restoringDrift I a / a =
      nonrootWeightedSum
        (fun d v => discrepancy I a d v * regularizedMass I a d v) L := by
  unfold restoringDrift bellmanDrift nonrootWeightedSum weightedLevel
  unfold discrepancy regularizedMass intervalMass
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro v hv
  field_simp [ha.ne']
end FD1D.V5.TreePolicy
