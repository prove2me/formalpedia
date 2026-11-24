-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.sgR_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:41:52.742363+00:00
-- url     : https://prove2.me/submissions/db4e1d04-0eaf-42dd-9877-0b456404a9cd

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_sg_mul_self

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
theorem _root_.solution (I : Finset (Fin n)) (m : Fin n) : ((sg I m : ℤ) : R) * ((sg I m : ℤ) : R) = 1 := by
  rw [← Int.cast_mul, sg_mul_self, Int.cast_one]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
