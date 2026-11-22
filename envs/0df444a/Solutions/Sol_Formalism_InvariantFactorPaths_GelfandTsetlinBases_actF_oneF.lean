-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.actF_oneF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:12:12.886572+00:00
-- url     : https://prove2.me/submissions/9d78fa50-d4e4-4a79-a7e8-0751cc2589cc

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
theorem _root_.solution (m : Matrix (Fin n) (Fin n) R) : actF (oneF : Form R n) m = oneF := by
  funext J
  simp only [actF, oneF, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold minorF
  by_cases hJ : J = ∅
  · subst hJ
    rw [dif_pos rfl, if_pos rfl]
    exact Matrix.det_eq_one_of_card_eq_zero (by first | exact Fintype.card_fin 0 | rfl | decide)
  · rw [dif_neg, if_neg hJ]
    simpa [Finset.card_eq_zero] using hJ
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
