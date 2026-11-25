-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.OrderLocusBlowup.orderAtLeastLocus_subset_preimage_of_isBlowupAlongIdealSheaf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:22:32.783+00:00
-- url     : https://prove2.me/submissions/58e62040-419b-42de-b317-c31e261ac369

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupIsoOffCenter
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderPullback
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_OrderUnderStalkIsomorphism
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_comap_of_isIso_stalkMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isIso_stalkMap_of_isBlowupAlongIdealSheaf
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealOrder_le_of_le
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
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.OrderLocusBlowup
namespace FunctorialResolution.EmbeddedResolution.OrderLocusBlowup
theorem _root_.solution {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z : X.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (A : X.IdealSheafData) (A₁ : X₁.IdealSheafData)
    (μ : ℕ) (hA : Blowup.exceptionalIdeal π Z ^ μ * A₁ = A.comap π)
    (hZ : (Z.support : Set ↥X) ⊆ orderAtLeastLocus A μ) :
    orderAtLeastLocus A₁ μ ⊆ (⇑π.base) ⁻¹' orderAtLeastLocus A μ := by
  intro x hx
  by_cases hxZ : π.base x ∈ Z.support
  · exact hZ hxZ
  · have := isIso_stalkMap_of_isBlowupAlongIdealSheaf π Z hπ x hxZ
    have hle : stalkIdeal (A.comap π) x ≤ stalkIdeal A₁ x := by
      rw [← hA, stalkIdeal_mul]
      exact le_trans Ideal.mul_le_inf inf_le_right
    have h2 : orderAt A₁ x ≤ orderAt (A.comap π) x := idealOrder_le_of_le hle
    have h3 : orderAt (A.comap π) x = orderAt A (π.base x) :=
      orderAt_comap_of_isIso_stalkMap π A x
    show (μ : ℕ∞) ≤ orderAt A (π.base x)
    calc (μ : ℕ∞) ≤ orderAt A₁ x := hx
      _ ≤ orderAt (A.comap π) x := h2
      _ = orderAt A (π.base x) := h3
end FunctorialResolution.EmbeddedResolution.OrderLocusBlowup
