-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:19.985877+00:00
-- url     : https://prove2.me/submissions/2f744dd5-5513-4c3f-b2f6-6518773be279

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_genMat_det_ne

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
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
variable {ι ζ : Type*} {n : ℕ}
variable (k : Type*) [Field k]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution (n : ℕ) : (genMat k n)⁻¹ * genMat k n = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (genMat_det_ne k n))
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
