-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.stalkIdeal_eq_stalkIdeal_monomialFactorIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:19:00.8698+00:00
-- url     : https://prove2.me/submissions/c750b8f2-72c9-4e29-8952-ca3a1495442a

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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_eq_prod_of_isMonomialOnOpen
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exponent_eq_orderAlongComponent
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_X_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_X_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_coordBasis_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_inducedBasis_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_tensorKaehlerBasis_mapBaseChange
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_isIrreducibleComponentOfSupport
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealSheafColon_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_support_iff_stalkIdeal_ne_top
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_monomialFactorIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_monomialPartAlongDivisor_of_mem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_monomialPartAlongDivisor_of_not_mem_support
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_unitMultiIndex_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.coordRingHom_X
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.algebraMap_X_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.algebraMap_X_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.coord_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.coord_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.JacobianCriterion.coordBasis_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.JacobianCriterion.inducedBasis_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.JacobianCriterion.tensorKaehlerBasis_mapBaseChange
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.idealSheafColon_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.pullbackCoord_def
attribute [local simp] FunctorialResolution.EmbeddedResolution.unitMultiIndex_apply


section
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}}
private theorem map_finRange_get_eq_map {α : Type*} {β : Type*} (l : List α) (g : α → β) :
    (List.finRange l.length).map (fun j => g (l.get j)) = l.map g := by
  refine List.ext_getElem (by simp) ?_
  intro n h1 h2
  simp
end FunctorialResolution.EmbeddedResolution
end
end

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
    (hI : NonzeroOnComponents I) (hsplit : IsMonomialSplitting E I M N) (x : X) :
    stalkIdeal M x = stalkIdeal (monomialFactorIdeal E I) x := by
  obtain ⟨U, hxU, a, haU⟩ := hsplit.monomial x
  have hmon : IsMonomialOnOpen E M U a := by
    show M.comap U.ι
        = ((List.finRange E.length).map (fun j => (E.get j).comap U.ι ^ a j)).prod
    rw [haU, Fin.prod_univ_def]
  have hstep : ∀ j : Fin E.length,
      stalkIdeal (E.get j) x ^ a j = stalkIdeal (monomialPartAlongDivisor I (E.get j)) x := by
    intro j
    have hmem : E.get j ∈ E := by simp
    by_cases hx : x ∈ ((E.get j).support : Set X)
    · obtain ⟨C, hC, hxC⟩ := exists_isIrreducibleComponentOfSupport (E.get j) x hx
      have hloc : IsEtaleLocallyCoordinateDivisor p (E.get j) :=
        isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE (E.get j) hmem
      rw [stalkIdeal_monomialPartAlongDivisor_of_mem p I hloc hC hxC,
        exponent_eq_orderAlongComponent p E hE hI hsplit U a hmon j hC x hxU hxC]
    · have h1 : stalkIdeal (E.get j) x = ⊤ := by
        by_contra hne
        exact hx ((mem_support_iff_stalkIdeal_ne_top (E.get j) x).mpr hne)
      rw [stalkIdeal_monomialPartAlongDivisor_of_not_mem_support I (E.get j) hx, h1,
        ← Ideal.one_eq_top, one_pow]
  have hlist : (List.finRange E.length).map (fun j => stalkIdeal (E.get j) x ^ a j)
      = E.map (fun D => stalkIdeal (monomialPartAlongDivisor I D) x) := by
    rw [← map_finRange_get_eq_map E (fun D => stalkIdeal (monomialPartAlongDivisor I D) x)]
    exact List.map_congr_left (fun j _ => hstep j)
  rw [stalkIdeal_eq_prod_of_isMonomialOnOpen E M U a hmon x hxU,
    stalkIdeal_monomialFactorIdeal E I x, hlist]
end FunctorialResolution.EmbeddedResolution
