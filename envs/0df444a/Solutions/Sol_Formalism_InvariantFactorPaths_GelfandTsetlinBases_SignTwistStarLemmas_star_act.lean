-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas.star_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:21:16.120869+00:00
-- url     : https://prove2.me/submissions/c1040831-996f-43f0-9a27-65fdacebece7

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_JacobiMinorProof
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_star_add
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_star_smul
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_star_wedge
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_actF_basisF
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_minorF_univ
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_star_basisF
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_actF_add
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_actF_oneF
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_actF_smul
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_actFormContract
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_actFormWedge
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_basisF_empty
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_contrF_smul
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_form_induction


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
theorem _root_.solution (m : (Matrix (Fin n) (Fin n) R)ˣ) (A : Form R n) :
    actF (star A) (↑m : Matrix (Fin n) (Fin n) R) =
      (↑m : Matrix (Fin n) (Fin n) R).det •
        star (actF A (↑m⁻¹ : Matrix (Fin n) (Fin n) R).transpose) := by
  refine form_induction (P := fun A => actF (star A) (↑m : Matrix (Fin n) (Fin n) R) =
      (↑m : Matrix (Fin n) (Fin n) R).det •
        star (actF A (↑m⁻¹ : Matrix (Fin n) (Fin n) R).transpose)) ?_ ?_ ?_ ?_ A
  · rw [actF_oneF, ← basisF_empty, star_basisF, actF_smul, actF_basisF]
    funext J
    simp only [Pi.smul_apply, smul_eq_mul, compl_empty, minorF_univ, basisF]
    split_ifs <;> ring
  · intro K K' h h'
    rw [star_add, actF_add, h, h', actF_add, star_add, smul_add]
  · intro c K h
    rw [star_smul, actF_smul, h, actF_smul, star_smul, smul_comm]
  · intro K X h
    rw [star_wedge, actFormContract R n _ X m, h, contrF_smul, actFormWedge R n K X, star_wedge]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
