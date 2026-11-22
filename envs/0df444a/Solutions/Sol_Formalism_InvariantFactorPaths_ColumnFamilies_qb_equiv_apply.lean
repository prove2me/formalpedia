-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_equiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:31:57.390326+00:00
-- url     : https://prove2.me/submissions/e473a9f7-5cf4-4701-a1dc-805e7d5e0a20

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {M : GLMod n} (CF : ColFam M) (j : CF.J) (i : M.ι) (K : TIdx (CF.mu j)) :
    ∑ k, M.A i k * (CF.ph j k K : GLCoord ℤ n) = ∑ K', (CF.ph j i K' : GLCoord ℤ n) * TMat (CF.mu j) K' K :=
  congrFun (congrFun (CF.equiv j) i) K
end Formalism.InvariantFactorPaths.ColumnFamilies
