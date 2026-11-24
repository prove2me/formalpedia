-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_torus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:52.046073+00:00
-- url     : https://prove2.me/submissions/652b3488-b012-4f12-b81a-f9d0379ce235

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SumIndicesEqSumColumns
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LamStrip
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_evGL_minorC
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_minor_diagonal
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_prod_single


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
theorem _root_.solution (b : ℕ) (k l : LamIdx n b) :
    evGL (torusPt n) (LamMat n b k l) = if k = l then AddMonoidAlgebra.single (ql_be b k) 1 else 0 := by
  rw [LamMat, qb_evGL_minorC]
  change Matrix.det (Matrix.of fun a b => Matrix.diagonal _ _ _) = _
  rw [qb_minor_diagonal, qb_prod_single]
  simp only [Subtype.ext_iff, ql_be]
end Formalism.InvariantFactorPaths.ColumnFamilies
