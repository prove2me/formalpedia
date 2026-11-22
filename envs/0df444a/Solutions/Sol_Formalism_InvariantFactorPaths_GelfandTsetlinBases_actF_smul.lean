-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.actF_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:12:18.357582+00:00
-- url     : https://prove2.me/submissions/f31af4ac-a963-4814-a310-3b7346e6cdbe

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract

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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
variable {R : Type*} [CommRing R] {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution (c : R) (K : Form R n) (m : Matrix (Fin n) (Fin n) R) :
    actF (c • K) m = c • actF K m := by
  funext J
  simp only [actF, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
