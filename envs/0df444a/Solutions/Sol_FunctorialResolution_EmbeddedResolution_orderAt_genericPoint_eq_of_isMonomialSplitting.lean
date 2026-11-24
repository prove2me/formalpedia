-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.orderAt_genericPoint_eq_of_isMonomialSplitting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:27:12.425534+00:00
-- url     : https://prove2.me/submissions/68ba0caa-89a8-4719-b483-0c0abdc34ca2

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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsIrreducibleComponentOfSupport_closure_genericPoint
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_eq_zero_iff_not_mem_support
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_mul


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
    (E : List X.IdealSheafData) (_hE : InStrictNormalCrossingPosition p E) {I M N : X.IdealSheafData}
    (_hI : NonzeroOnComponents I) (hsplit : IsMonomialSplitting E I M N)
    {D : X.IdealSheafData} (hD : D ∈ E) {C : Set X} (hC : IsIrreducibleComponentOfSupport D C) :
    orderAt M hC.isIrreducible.genericPoint = orderAt I hC.isIrreducible.genericPoint := by
  have hmax' : ∀ C' : Set X, IsIrreducible C' → C' ⊆ (D.support : Set X) → C ⊆ C' → C' ⊆ C := by
    intro C' h1 h2 h3
    have he := hC.maximal C' h1 h3 h2
    intro y hy
    rw [he] at hy
    exact hy
  have hNC : ¬ C ⊆ (N.support : Set X) :=
    hsplit.transversal D hD C hC.isIrreducible hC.subset_support hmax'
  have hηN : hC.isIrreducible.genericPoint ∉ N.support := by
    intro h
    refine hNC ?_
    rw [← hC.closure_genericPoint]
    exact (N.support.2).closure_subset_iff.mpr (Set.singleton_subset_iff.mpr h)
  have h0 : orderAt N hC.isIrreducible.genericPoint = 0 :=
    (orderAt_eq_zero_iff_not_mem_support N hC.isIrreducible.genericPoint).mpr hηN
  rw [hsplit.eq_mul, orderAt_mul k p M N hC.isIrreducible.genericPoint, h0, add_zero]
end FunctorialResolution.EmbeddedResolution
