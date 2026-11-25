-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.eq_nonMonomialFactorIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:01:15.315917+00:00
-- url     : https://prove2.me/submissions/11279d96-73fd-4d42-a856-f6c9398d8601

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_ControlledTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IrreducibleComponentsOfSupport
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtGenericPoint
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtMultiplicativity
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderPullback
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialPartAlongDivisor
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialSplitting
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialSplittingUniqueness
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_eq_monomialFactorIdeal
import Theorems.Thm_FunctorialResolution_Blowup_IsLocallyGeneratedByNonZeroDivisor_eq_of_mul_eq_mul
import Theorems.Thm_FunctorialResolution_Blowup_IsLocallyGeneratedByNonZeroDivisor_mul_idealSheafColon
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isLocallyGeneratedByNonZeroDivisor_monomialFactorIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_iff_forall_stalkIdeal_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_nonMonomialFactorIdeal_eq_idealSheafColon
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {k : Type u} [Field k] [CharZero k]
    [TopologicalSpace.NoetherianSpace ↥X] [IsLocallyNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E) {I M N : X.IdealSheafData}
    (hI : NonzeroOnComponents I) (hsplit : IsMonomialSplitting E I M N) :
    N = nonMonomialFactorIdeal E I := by
  have hM : M = monomialFactorIdeal E I := eq_monomialFactorIdeal p E hE hI hsplit
  have hF : Blowup.IsLocallyGeneratedByNonZeroDivisor (monomialFactorIdeal E I) :=
    isLocallyGeneratedByNonZeroDivisor_monomialFactorIdeal p E I hE
  have hIM : I ≤ monomialFactorIdeal E I := by
    rw [← hM, hsplit.eq_mul]
    refine (le_iff_forall_stalkIdeal_le _ _).mpr (fun y => ?_)
    rw [stalkIdeal_mul]
    exact Ideal.mul_le_inf.trans inf_le_left
  have hmul : monomialFactorIdeal E I * N
      = monomialFactorIdeal E I * nonMonomialFactorIdeal E I := by
    rw [nonMonomialFactorIdeal_eq_idealSheafColon, hF.mul_idealSheafColon hIM, ← hM]
    exact hsplit.eq_mul.symm
  exact hF.eq_of_mul_eq_mul hmul
end FunctorialResolution.EmbeddedResolution
