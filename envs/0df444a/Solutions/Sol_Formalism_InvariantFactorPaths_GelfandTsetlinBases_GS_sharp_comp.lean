-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.sharp_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:47:22.290453+00:00
-- url     : https://prove2.me/submissions/f9fccce6-5453-44a7-a2c1-68681f97686c

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_GenSpaceFacts
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_sharp_C
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
theorem _root_.solution (x xi y yi : Matrix (Fin n) (Fin n) A) (P : MvPolynomial (LVar ι ζ n) A) :
    sharpHom isVec S x xi (sharpHom isVec S y yi P) = sharpHom isVec S (x * y) (yi * xi) P := by
  suffices hh : (sharpHom (ζ := ζ) isVec S x xi).comp (sharpHom isVec S y yi) =
      sharpHom isVec S (x * y) (yi * xi) from DFunLike.congr_fun hh P
  apply MvPolynomial.algHom_ext
  rintro (⟨i, a⟩ | z)
  · by_cases h1 : i ∈ S
    · cases h3 : isVec i
      · simp only [AlgHom.comp_apply, sharp_covec h1 h3, map_sum, map_mul, sharp_C, Matrix.mul_apply,
          Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
        ring
      · simp only [AlgHom.comp_apply, sharp_vec h1 h3, map_sum, map_mul, sharp_C, Matrix.mul_apply,
          Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
        ring
    · simp [sharp_out h1]
  · simp [sharp_further]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
