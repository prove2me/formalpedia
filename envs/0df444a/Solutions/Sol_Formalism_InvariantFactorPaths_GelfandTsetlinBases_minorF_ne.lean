-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.minorF_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:41:29.745529+00:00
-- url     : https://prove2.me/submissions/6cb5ae5c-3d19-4ebb-820b-0cd67c6de781

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
theorem _root_.solution (m : Matrix (Fin n) (Fin n) R) {I J : Finset (Fin n)} (h : J.card ≠ I.card) :
    minorF m I J = 0 := by
  unfold minorF
  rw [dif_neg h]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
