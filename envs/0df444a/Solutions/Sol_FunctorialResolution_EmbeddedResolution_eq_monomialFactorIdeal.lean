-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.eq_monomialFactorIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:06:11.296367+00:00
-- url     : https://prove2.me/submissions/497519e8-efef-4805-b09d-998ac95a1cb9

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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_eq_stalkIdeal_monomialFactorIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_iff_forall_stalkIdeal_le


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
    M = monomialFactorIdeal E I := by
  have hstalk : ∀ x : X, stalkIdeal M x = stalkIdeal (monomialFactorIdeal E I) x :=
    fun x => stalkIdeal_eq_stalkIdeal_monomialFactorIdeal p E hE hI hsplit x
  refine le_antisymm ?_ ?_
  · exact (le_iff_forall_stalkIdeal_le M (monomialFactorIdeal E I)).mpr
      (fun x => le_of_eq (hstalk x))
  · exact (le_iff_forall_stalkIdeal_le (monomialFactorIdeal E I) M).mpr
      (fun x => le_of_eq (hstalk x).symm)
end FunctorialResolution.EmbeddedResolution
