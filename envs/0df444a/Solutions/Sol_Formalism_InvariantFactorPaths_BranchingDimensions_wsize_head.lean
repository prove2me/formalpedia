-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.wsize_head
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:15.128367+00:00
-- url     : https://prove2.me/submissions/46e98290-9e18-402a-ac87-78614908adee

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_stage_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
open Letters
variable {D : Letters} {mu : D.Stages}
namespace Formalism.InvariantFactorPaths.BranchingDimensions
theorem _root_.solution (j : ℕ) (hj : j ≤ D.k) (hH : ∀ m, m < j → ent mu (D.n0 + j) m = D.be) :
    wsize D.k (ent mu (D.n0 + j)) = (j : ℤ) * D.be + wsize (D.k - j) (stage mu (D.n0 + j)) := by
  unfold wsize
  have hk : D.k = j + (D.k - j) := by omega
  conv_lhs => rw [hk]
  rw [Finset.sum_range_add, Finset.sum_congr rfl (fun m hm => hH m (Finset.mem_range.1 hm)),
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [stage_add, Nat.add_comm m j]
end Formalism.InvariantFactorPaths.BranchingDimensions
