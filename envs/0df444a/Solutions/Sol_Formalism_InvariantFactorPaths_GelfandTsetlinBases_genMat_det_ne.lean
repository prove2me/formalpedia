-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat_det_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:33.236466+00:00
-- url     : https://prove2.me/submissions/46b6709d-fcb8-4ab9-b4e2-76eff56ca1d6

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_genMat_eq

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
theorem _root_.solution (n : ℕ) : (genMat k n).det ≠ 0 := by
  rw [genMat_eq, ← RingHom.map_det]
  exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (Matrix.det_mvPolynomialX_ne_zero (Fin n) k)
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
