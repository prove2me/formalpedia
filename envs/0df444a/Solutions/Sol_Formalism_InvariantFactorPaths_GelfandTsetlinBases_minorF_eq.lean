-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.minorF_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:12:20.104668+00:00
-- url     : https://prove2.me/submissions/187b9472-22f7-4562-a5e0-16cb925522b0

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
theorem _root_.solution {d : ℕ} (m : Matrix (Fin n) (Fin n) R) {I J : Finset (Fin n)} (hI : I.card = d)
    (hJ : J.card = d) :
    minorF m I J = (m.submatrix (I.orderEmbOfFin hI) (J.orderEmbOfFin hJ)).det := by
  subst hI
  unfold minorF
  rw [dif_pos hJ]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
