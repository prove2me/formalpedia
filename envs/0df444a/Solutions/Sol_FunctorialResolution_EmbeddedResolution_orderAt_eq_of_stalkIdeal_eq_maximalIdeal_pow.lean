-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.orderAt_eq_of_stalkIdeal_eq_maximalIdeal_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:27:11.772859+00:00
-- url     : https://prove2.me/submissions/aabb8a7f-ae78-408b-8423-f22dcfcf1e4d

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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_orderAt_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_eq_top_iff


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
theorem _root_.solution [IsLocallyNoetherian X]
    (M : X.IdealSheafData) (η : X) (a : ℕ)
    (hM : stalkIdeal M η = IsLocalRing.maximalIdeal ↥(X.presheaf.stalk η) ^ a)
    (hfin : orderAt M η ≠ ⊤) :
    orderAt M η = (a : ℕ∞) := by
  have hnoe : IsNoetherianRing (X.presheaf.stalk η) := inferInstance
  have hbot : stalkIdeal M η ≠ ⊥ := fun h => hfin ((orderAt_eq_top_iff M η).mpr h)
  have hle : (a : ℕ∞) ≤ orderAt M η := (le_orderAt_iff M η a).mpr (le_of_eq hM)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  have hordn : orderAt M η = (n : ℕ∞) := hn.symm
  have han : a ≤ n := by
    rw [hordn] at hle
    exact_mod_cast hle
  have hna : n ≤ a := by
    by_contra hc
    push Not at hc
    have hc' : a + 1 ≤ n := by omega
    have h1 : ((a + 1 : ℕ) : ℕ∞) ≤ orderAt M η := by
      rw [hordn]
      exact_mod_cast hc'
    have h2 : stalkIdeal M η ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk η) ^ (a + 1) :=
      (le_orderAt_iff M η (a + 1)).mp h1
    have hps : IsLocalRing.maximalIdeal (X.presheaf.stalk η) •
        (IsLocalRing.maximalIdeal (X.presheaf.stalk η) ^ a)
        = IsLocalRing.maximalIdeal (X.presheaf.stalk η) ^ (a + 1) := by
      rw [Ideal.smul_eq_mul, pow_succ, mul_comm]
    have hsm : (IsLocalRing.maximalIdeal (X.presheaf.stalk η) ^ a) ≤
        IsLocalRing.maximalIdeal (X.presheaf.stalk η) •
          (IsLocalRing.maximalIdeal (X.presheaf.stalk η) ^ a) := by
      rw [hps, ← hM]
      exact h2
    have hz : (IsLocalRing.maximalIdeal (X.presheaf.stalk η) ^ a) = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
        (IsLocalRing.maximalIdeal (X.presheaf.stalk η))
        (IsLocalRing.maximalIdeal (X.presheaf.stalk η) ^ a)
        (IsNoetherian.noetherian _) hsm
        (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    exact hbot (by rw [hM, hz])
  rw [hordn]
  exact_mod_cast le_antisymm hna han
end FunctorialResolution.EmbeddedResolution
