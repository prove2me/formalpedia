-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.exponent_le_orderAlongComponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:45:05.856515+00:00
-- url     : https://prove2.me/submissions/cd402ca1-d04c-4e2b-96f6-f1c622f59fcd

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
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_X_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_X_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsIrreducibleComponentOfSupport_closure_genericPoint
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsIrreducibleComponentOfSupport_genericPoint_mem_support
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_coordBasis_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_inducedBasis_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_tensorKaehlerBasis_mapBaseChange
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coe_orderAlongComponent_eq_orderAt_genericPoint
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealSheafColon_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_iff_forall_stalkIdeal_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_orderAt_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_support_iff_stalkIdeal_le_maximalIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_le_of_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_mul
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_unitMultiIndex_apply
import Theorems.Thm_Ideal_list_prod_le_getElem
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
    (E : List X.IdealSheafData) (_hE : InStrictNormalCrossingPosition p E) {I M N : X.IdealSheafData}
    (hI : NonzeroOnComponents I) (hsplit : IsMonomialSplitting E I M N)
    (U : X.Opens) (a : Fin E.length → ℕ) (ha : IsMonomialOnOpen E M U a)
    (l : Fin E.length) {C' : Set X} (hC' : IsIrreducibleComponentOfSupport (E.get l) C')
    (x : X) (hxU : x ∈ U) (hxC : x ∈ C') :
    a l ≤ orderAlongComponent I hC'.isIrreducible := by
  have hxcl : x ∈ closure ({hC'.isIrreducible.genericPoint} : Set X) := by
    rw [hC'.closure_genericPoint]
    exact hxC
  have hηU : hC'.isIrreducible.genericPoint ∈ U := by
    obtain ⟨z, hzU, hz⟩ := mem_closure_iff.mp hxcl (U : Set X) U.isOpen hxU
    rw [Set.mem_singleton_iff] at hz
    rw [← hz]
    exact hzU
  have hprod : stalkIdeal M hC'.isIrreducible.genericPoint =
      ((List.finRange E.length).map
        (fun j => stalkIdeal (E.get j) hC'.isIrreducible.genericPoint ^ a j)).prod :=
    stalkIdeal_eq_prod_of_isMonomialOnOpen E M U a ha hC'.isIrreducible.genericPoint hηU
  have hlen : (l : ℕ) <
      ((List.finRange E.length).map
        (fun j => stalkIdeal (E.get j) hC'.isIrreducible.genericPoint ^ a j)).length := by
    simp
  have hget : ((List.finRange E.length).map
        (fun j => stalkIdeal (E.get j) hC'.isIrreducible.genericPoint ^ a j))[(l : ℕ)]'hlen
      = stalkIdeal (E.get l) hC'.isIrreducible.genericPoint ^ a l := by
    simp
  have h1 : stalkIdeal M hC'.isIrreducible.genericPoint ≤
      stalkIdeal (E.get l) hC'.isIrreducible.genericPoint ^ a l := by
    rw [hprod, ← hget]
    exact Ideal.list_prod_le_getElem _ _ hlen
  have hle : stalkIdeal (E.get l) hC'.isIrreducible.genericPoint ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk hC'.isIrreducible.genericPoint) :=
    (mem_support_iff_stalkIdeal_le_maximalIdeal (E.get l)
      hC'.isIrreducible.genericPoint).mp hC'.genericPoint_mem_support
  have h2 : (a l : ℕ∞) ≤ orderAt M hC'.isIrreducible.genericPoint :=
    (le_orderAt_iff M hC'.isIrreducible.genericPoint (a l)).mpr
      (h1.trans (Ideal.pow_right_mono hle (a l)))
  have hIM : I ≤ M := by
    rw [hsplit.eq_mul]
    refine (le_iff_forall_stalkIdeal_le _ _).mpr (fun y => ?_)
    rw [stalkIdeal_mul]
    exact Ideal.mul_le_inf.trans inf_le_left
  have h3 : orderAt M hC'.isIrreducible.genericPoint ≤
      orderAt I hC'.isIrreducible.genericPoint :=
    orderAt_le_of_le hIM hC'.isIrreducible.genericPoint
  have h4 : (a l : ℕ∞) ≤ (orderAlongComponent I hC'.isIrreducible : ℕ∞) := by
    rw [coe_orderAlongComponent_eq_orderAt_genericPoint hC' hI]
    exact h2.trans h3
  exact_mod_cast h4
end FunctorialResolution.EmbeddedResolution
