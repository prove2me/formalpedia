-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0.eps_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:06:15.321912+00:00
-- url     : https://prove2.me/submissions/6cd341dc-c663-4d2d-8a67-9e0b54273210

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_ValuationProductsComponents
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents

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
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
variable {R : Type} [CommRing R] {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
theorem _root_.solution (I : Finset (Fin n)) : eps I = (-1) ^ (∑ a ∈ I, a.val + I.card * (n + 1)) := by
  unfold eps
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  simp only [add_assoc, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
  ring
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
