-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.sharp_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:23:46.575875+00:00
-- url     : https://prove2.me/submissions/f17a0c36-9012-4be0-a823-22fa7a940d5a

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_GenSpaceFacts
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_sharp_vec
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_sharp_covec
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_sharp_out
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_sharp_further

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
variable {ι ζ : Type*} {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
variable {A B : Type*} [CommRing A] [CommRing B]
variable {isVec S}
variable (isVec S)
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
theorem _root_.solution (θ : A →+* B) (g gi : Matrix (Fin n) (Fin n) A) (P : MvPolynomial (LVar ι ζ n) A) :
    map θ (sharpHom isVec S g gi P) = sharpHom isVec S (g.map θ) (gi.map θ) (map θ P) := by
  suffices hh : (map θ).comp (sharpHom (ζ := ζ) isVec S g gi).toRingHom =
      (sharpHom (ζ := ζ) isVec S (g.map θ) (gi.map θ)).toRingHom.comp (map θ) from
    DFunLike.congr_fun hh P
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · rintro (⟨i, a⟩ | z)
    · by_cases h1 : i ∈ S
      · cases h3 : isVec i
        · simp [sharp_covec h1 h3]
        · simp [sharp_vec h1 h3]
      · simp [sharp_out h1]
    · simp [sharp_further]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
