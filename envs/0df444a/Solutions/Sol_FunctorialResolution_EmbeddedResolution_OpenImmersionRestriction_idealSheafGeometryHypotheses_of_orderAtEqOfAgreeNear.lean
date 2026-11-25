-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.idealSheafGeometryHypotheses_of_orderAtEqOfAgreeNear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:59:39.19847+00:00
-- url     : https://prove2.me/submissions/af546309-caea-486d-9a1f-75001db935ec

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderPullback
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_RestrictionToOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_VanishingIdealAssignment
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_agreeNear_comap___bbe540cce3bf
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_orderAt_comap___3b37585930bd
import Theorems.Thm_P2M_RH_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul_ffd4b47c5064b9ee
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_X_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_X_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_agreeNear_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_nonzeroOnComponents_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_comap
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
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal


section
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
private theorem comap_opens_eq_of_le {W : Scheme.{u}} {I J : W.IdealSheafData} {U U' : W.Opens}
    (h : U' ≤ U) (hEq : I.comap U.ι = J.comap U.ι) :
    I.comap U'.ι = J.comap U'.ι := by
  have hι : W.homOfLE h ≫ U.ι = U'.ι := by simp
  rw [← hι, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, hEq]
end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
namespace FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
theorem _root_.solution
    (h1 : VanishingOrderOneOnSmoothDivisor.{u}) (h2 : AgreeNearVanishingComapSubscheme.{u})
    (h3 : VanishingComapOpens.{u}) (h4 : OrderAtEqOfAgreeNear.{u}) :
    IdealSheafGeometryHypotheses vanishingIdealAssignment.{u} :=
  { agreeNear_comap := agreeNear_comap_ι
    agreeNear_trans := by
      intro W I J K x hIJ hJK
      obtain ⟨U1, hx1, e1⟩ := (agreeNear_iff I J x).mp hIJ
      obtain ⟨U2, hx2, e2⟩ := (agreeNear_iff J K x).mp hJK
      exact (agreeNear_iff I K x).mpr
        ⟨U1 ⊓ U2, ⟨hx1, hx2⟩,
          (comap_opens_eq_of_le inf_le_left e1).trans (comap_opens_eq_of_le inf_le_right e2)⟩
    comap_mul := fun W X f I J => Scheme.IdealSheafData.comap_mul I J f
    base_comp := fun X Y Z f g x => by simp
    isClosed_support := fun W I => I.support.isClosed
    isClosedEmbedding_subschemeι := fun W I =>
      IsClosedImmersion.isClosedEmbedding (f := I.subschemeι)
    isEmbedding_ι := fun W U => U.ι.isOpenEmbedding.toIsEmbedding
    isOpen_opens := fun W U => U.2
    orderAt_comap := orderAt_comap_ι
    orderAt_congr := h4
    orderAt_vanishing_eq_one := h1
    range_ι := fun W U => by simp
    range_subschemeι := fun W I => by simp
    support_mul := fun W I J => by
      rw [Scheme.IdealSheafData.support_mul, TopologicalSpace.Closeds.coe_sup]
    not_subset_support_of_nonzeroOnComponents := fun W I h => (nonzeroOnComponents_iff I).mp h
    support_vanishing := fun W T => by simp [vanishingIdealAssignment]
    top_mul := fun W I => by simp
    agreeNear_vanishing_restrict := h2
    comap_vanishing := h3 }
end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
