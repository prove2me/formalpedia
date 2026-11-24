-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.genMat_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:06.868587+00:00
-- url     : https://prove2.me/submissions/1ea32fc0-9387-4c47-a437-8c557f835222

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe

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
theorem _root_.solution (n : ℕ) : genMat k n =
    (algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n)).mapMatrix (Matrix.mvPolynomialX (Fin n) (Fin n) k) := by
  ext a b
  simp [genMat, Matrix.mvPolynomialX]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
