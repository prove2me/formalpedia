-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.contrF_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:49.625415+00:00
-- url     : https://prove2.me/submissions/9bf5651d-e2f4-4f8d-80a0-05d44ab3ac30

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
    contrF (K + K') X = contrF K X + contrF K' X := by
  funext I
  simp only [contrF, Pi.add_apply, mul_add, Finset.sum_add_distrib]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
