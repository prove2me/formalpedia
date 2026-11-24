-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.sum_emb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:47.208715+00:00
-- url     : https://prove2.me/submissions/1433177d-22a7-4c3a-b950-f31f3205e18c

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
theorem _root_.solution {d : ℕ} {J : Finset (Fin n)} (h : J.card = d) (f : Fin n → R) :
    ∑ b ∈ J, f b = ∑ j, f (J.orderEmbOfFin h j) := by
  conv_lhs => rw [← Finset.image_orderEmbOfFin_univ J h]
  rw [Finset.sum_image (fun x _ y _ hxy => (J.orderEmbOfFin h).injective hxy)]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
