-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas.jacobi_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:33:51.583218+00:00
-- url     : https://prove2.me/submissions/57780140-3f71-4580-88d7-2e0d6098e7f6

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_JacobiMinorProof
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_actF_basisF
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_star_basisF
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_star_act
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_actF_smul


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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
variable {R : Type} [CommRing R] {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
theorem _root_.solution (m : (Matrix (Fin n) (Fin n) R)ˣ) (I J : Finset (Fin n)) :
    (↑m : Matrix (Fin n) (Fin n) R).det * minorF (↑m⁻¹ : Matrix (Fin n) (Fin n) R).transpose I J =
      (-1) ^ (epsN Iᶜ + epsN Jᶜ) * minorF (↑m : Matrix (Fin n) (Fin n) R) Iᶜ Jᶜ := by
  have h := congrFun (star_act m (basisF I)) Jᶜ
  rw [star_basisF, actF_smul, actF_basisF, actF_basisF] at h
  simp only [Pi.smul_apply, smul_eq_mul, star, compl_compl] at h
  have e : ((-1 : R) ^ epsN Jᶜ) * ((-1 : R) ^ epsN Jᶜ) = 1 := by
    rw [← mul_pow]; simp
  rw [pow_add]
  linear_combination ((-1 : R) ^ epsN Jᶜ) * (-h) - ((↑m : Matrix (Fin n) (Fin n) R).det * minorF (↑m⁻¹ : Matrix (Fin n) (Fin n) R).transpose I J) * e
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
