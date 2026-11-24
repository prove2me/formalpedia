-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.stalkIdeal_componentPowerIdeal_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:08:37.828321+00:00
-- url     : https://prove2.me/submissions/672069bc-071c-44bd-ad0b-e912a8b55a3d

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_ControlledTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IrreducibleComponentsOfSupport
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtGenericPoint
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialSplitting
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialPartAlongDivisor
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_componentPowerIdeal_of_not_isIrreducibleComponentOfSupport
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_componentPowerIdeal_of_isIrreducibleComponentOfSupport
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_support_iff_stalkIdeal_ne_top
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_pow
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_top


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
variable {k : Type u} [Field k]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (I D : X.IdealSheafData) (C : Set X) {x : X}
    (hx : x ∉ C) : stalkIdeal (componentPowerIdeal I D C) x = ⊤ := by
  by_cases hC : IsIrreducibleComponentOfSupport D C
  · have htop : stalkIdeal (Scheme.IdealSheafData.vanishingIdeal
        (⟨C, hC.isClosed⟩ : TopologicalSpace.Closeds ↥X)) x = ⊤ := by
      by_contra h
      have hmem : x ∈ ((Scheme.IdealSheafData.vanishingIdeal
          (⟨C, hC.isClosed⟩ : TopologicalSpace.Closeds ↥X)).support : Set ↥X) :=
        (mem_support_iff_stalkIdeal_ne_top _ x).mpr h
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at hmem
      exact hx hmem
    rw [componentPowerIdeal_of_isIrreducibleComponentOfSupport I D hC, stalkIdeal_pow, htop, ← Ideal.one_eq_top,
      one_pow]
  · rw [componentPowerIdeal_of_not_isIrreducibleComponentOfSupport I D hC, stalkIdeal_top]
end FunctorialResolution.EmbeddedResolution
