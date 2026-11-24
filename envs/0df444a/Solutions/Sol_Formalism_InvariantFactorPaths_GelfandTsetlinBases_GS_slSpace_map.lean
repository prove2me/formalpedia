-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.slSpace_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:47:23.272355+00:00
-- url     : https://prove2.me/submissions/4c14acba-7fba-4e3b-86af-62c8ebc5fbec

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_GenSpaceFacts
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_slc_comp
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_slc_algHom

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
variable {k : Type*} [Field k] {σ : Type*}
variable {A B D : Type*} [CommRing A] [CommRing B] [CommRing D] [Algebra k A] [Algebra k B] [Algebra k D]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
theorem _root_.solution (θ : A →ₐ[k] B) (hθ : Function.Injective θ) (P : MvPolynomial σ A) :
    slSpace (k := k) (map (θ : A →+* B) P) = slSpace (k := k) P := by
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective θ.toLinearMap (LinearMap.ker_eq_bot.mpr hθ)
  apply le_antisymm
  · rintro _ ⟨ℓ, rfl⟩
    refine ⟨ℓ ∘ₗ θ.toLinearMap, ?_⟩
    change slc _ _ = slc _ _
    rw [← slc_algHom, slc_comp]
  · rintro _ ⟨ℓ, rfl⟩
    refine ⟨ℓ ∘ₗ r, ?_⟩
    change slc _ _ = slc _ _
    rw [← slc_algHom, slc_comp, LinearMap.comp_assoc, hr, LinearMap.comp_id]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
