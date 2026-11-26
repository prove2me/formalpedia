-- Prove2me | solution 1 for FD1D.V5.TreePolicy.local_bellman_inequality_separated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:00:10.45177+00:00
-- url     : https://prove2.me/submissions/1cf485b8-daee-4a7b-899d-42615d1ec1e5

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
import Theorems.Thm_FD1D_V5_TreePolicy_local_bellman_inequality
import Theorems.Thm_FD1D_V5_LocalBellman_local_bellman_inequality


set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}
namespace FD1D.V5.TreePolicy
theorem _root_.solution
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m)
    (d : ℕ) (hdL : d < L) (v : DyadicNode d) :
    childAverage
          (fun d v => discrepancy I a d v *
            regularizedMass I a d v) d v +
        childAverage (bellmanValue I a) d v -
        bellmanValue I a d v ≥
      (childAverage (fun d v => rate I a d v ^ 2) d v -
          rate I a d v ^ 2) / 1000 +
        imbalance I a d v ^ 2 / (1000 * a ^ 2) := by
  have hlocal := local_bellman_inequality I ha hm d hdL v
  calc
    (childAverage (fun d v => rate I a d v ^ 2) d v -
          rate I a d v ^ 2) / 1000 +
        imbalance I a d v ^ 2 / (1000 * a ^ 2) =
      (childAverage (fun d v => rate I a d v ^ 2) d v -
          rate I a d v ^ 2 +
          imbalance I a d v ^ 2 / a ^ 2) / 1000 := by
            field_simp [ha.ne'] <;> ring
    _ ≤ _ := hlocal
end FD1D.V5.TreePolicy
