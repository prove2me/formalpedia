-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.tw_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:14.624912+00:00
-- url     : https://prove2.me/submissions/9d45f3ef-08b6-4ea8-bc13-995a4df79814

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_lp_coeff_TC
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_lp_coeff_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_tw_monomial

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
variable {ι ζ : Type*} {n : ℕ} {L : Type*} [CommRing L]
variable (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution (g gi : Matrix (Fin n) (Fin n) L) (last : Bool) (H : MvPolynomial (LVar ι ζ n) L) (j : ℤ) :
    (tw isVec S g gi last H).coeff j =
      sharpHom isVec S g gi
        (∑ e ∈ H.support.filter (fun e => wExp isVec S last e = j), monomial e (coeff e H)) := by
  conv_lhs => rw [H.as_sum]
  rw [map_sum, lp_coeff_sum, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [tw_monomial, lp_coeff_TC]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
