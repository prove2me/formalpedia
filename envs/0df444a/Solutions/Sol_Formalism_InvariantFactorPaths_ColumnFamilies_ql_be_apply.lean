-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_be_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:51:38.071394+00:00
-- url     : https://prove2.me/submissions/09a0dfec-6f82-4943-b0ce-7e8f2d8205e3

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SumIndicesEqSumColumns
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LamStrip

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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (b : ℕ) (L : LamIdx n b) (a : Fin n) : ql_be b L a = if a ∈ L.1 then 1 else 0 := by
  simp [ql_be, Finset.sum_apply, Pi.single_apply]
end Formalism.InvariantFactorPaths.ColumnFamilies
