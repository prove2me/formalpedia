-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.wedgeF_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:05:23.255789+00:00
-- url     : https://prove2.me/submissions/3a8e3254-5469-474c-9fcc-9f1da73059e0

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
theorem _root_.solution (K K' : Form R n) (X : Fin n → R) :
    wedgeF (K + K') X = wedgeF K X + wedgeF K' X := by
  funext I
  simp only [wedgeF, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
