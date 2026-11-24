-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.actF_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:49.645846+00:00
-- url     : https://prove2.me/submissions/c7b9a832-43d7-4281-b589-1ef92e74e46c

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
theorem _root_.solution (m : Matrix (Fin n) (Fin n) R) : actF (0 : Form R n) m = 0 := by
  funext J
  simp [actF]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
