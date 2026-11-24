-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.orderAt_eq_one_of_stalkIdeal_eq_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:05:32.485506+00:00
-- url     : https://prove2.me/submissions/c9c6cb8f-ac1a-4ca0-91f6-34be987bd88d

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_eq_one_iff
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_affineOpens_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace FunctorialResolution.EmbeddedResolution
open AlgebraicGeometry TopologicalSpace
universe u
variable {X : Scheme.{u}}
private theorem maximalIdeal_not_le_sq {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (h : IsLocalRing.maximalIdeal R ≠ ⊥) :
    ¬ IsLocalRing.maximalIdeal R ≤ IsLocalRing.maximalIdeal R ^ 2 := by
  intro hle
  refine h (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R)
      (IsLocalRing.maximalIdeal R) (IsNoetherian.noetherian _) ?_ ?_)
  · rw [Ideal.smul_eq_mul, ← pow_two]
    exact hle
  · exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open AlgebraicGeometry TopologicalSpace
universe u
variable {X : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (x : X)
    (h : stalkIdeal I x = IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hne : IsLocalRing.maximalIdeal (X.presheaf.stalk x) ≠ ⊥) :
    orderAt I x = 1 := by
  obtain ⟨U, hxU⟩ := X.exists_affineOpens_mem x
  have hxU' : x ∈ U.1 := hxU
  have hnoeth : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let germAlgebra : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
    (X.presheaf.germ U.1 x hxU').hom.toAlgebra
  have hloc : IsLocalization (U.2.primeIdealOf ⟨x, hxU'⟩).asIdeal.primeCompl
      (X.presheaf.stalk x) := U.2.isLocalization_stalk ⟨x, hxU'⟩
  have : IsNoetherianRing (X.presheaf.stalk x) :=
    IsLocalization.isNoetherianRing (U.2.primeIdealOf ⟨x, hxU'⟩).asIdeal.primeCompl _ hnoeth
  rw [orderAt_eq_one_iff]
  refine ⟨h.le, ?_⟩
  rw [h]
  exact maximalIdeal_not_le_sq hne
end FunctorialResolution.EmbeddedResolution
