-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.sg_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:47.321651+00:00
-- url     : https://prove2.me/submissions/4a5aeeaf-ec3d-4377-8331-ec4683381f64

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
theorem _root_.solution (I : Finset (Fin n)) (m : Fin n) : sg I m * sg I m = 1 := by
  rw [sg, ← mul_pow, neg_one_mul, neg_neg, one_pow]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
