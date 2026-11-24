-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.HStrip.diff_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:40.570598+00:00
-- url     : https://prove2.me/submissions/706daf6f-c434-4723-bec5-9f7e02d9d87a

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs

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
namespace Formalism.InvariantFactorPaths.BranchingDimensions
namespace HStrip
theorem _root_.solution {n : ℕ} {a b : ℕ → ℤ} (h : HStrip n a b) (m : ℕ) (hm : m < n) :
    b m - a m ≤ wsize n b - wsize n a := by
  unfold wsize
  rw [← Finset.sum_sub_distrib]
  exact Finset.single_le_sum (f := fun j => b j - a j)
    (fun j hj => sub_nonneg.mpr (h.1 j (Finset.mem_range.mp hj))) (Finset.mem_range.mpr hm)
end HStrip
end Formalism.InvariantFactorPaths.BranchingDimensions
