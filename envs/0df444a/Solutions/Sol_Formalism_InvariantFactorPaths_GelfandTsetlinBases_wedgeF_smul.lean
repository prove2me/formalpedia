-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.wedgeF_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:05:27.383031+00:00
-- url     : https://prove2.me/submissions/56fa3975-f08c-466e-96f1-ef9021cb5e1a

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
theorem _root_.solution (c : R) (K : Form R n) (X : Fin n → R) :
    wedgeF (c • K) X = c • wedgeF K X := by
  funext I
  simp only [wedgeF, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
