-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.actF_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:40:50.570458+00:00
-- url     : https://prove2.me/submissions/c07efc39-ad83-4716-b7ef-8a4198e65785

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
theorem _root_.solution (K K' : Form R n) (m : Matrix (Fin n) (Fin n) R) :
    actF (K + K') m = actF K m + actF K' m := by
  funext J
  simp only [actF, Pi.add_apply, add_mul, Finset.sum_add_distrib]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
