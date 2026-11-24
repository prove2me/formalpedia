-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.orderAt_ne_top_of_stalkIdeal_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:36.649+00:00
-- url     : https://prove2.me/submissions/6e9d799e-28c0-4d01-a6be-873fa4c15195

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_eq_idealOrder
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_affineOpens_mem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealOrder_ne_top_of_ne_bot


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open AlgebraicGeometry TopologicalSpace
universe u
variable {X : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (x : X) (h : stalkIdeal I x ≠ ⊥) : orderAt I x ≠ ⊤ := by
  obtain ⟨U, hxU⟩ := X.exists_affineOpens_mem x
  have hxU' : x ∈ U.1 := hxU
  have hnoeth : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let germAlgebra : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
    (X.presheaf.germ U.1 x hxU').hom.toAlgebra
  have hloc : IsLocalization (U.2.primeIdealOf ⟨x, hxU'⟩).asIdeal.primeCompl
      (X.presheaf.stalk x) := U.2.isLocalization_stalk ⟨x, hxU'⟩
  have : IsNoetherianRing (X.presheaf.stalk x) :=
    IsLocalization.isNoetherianRing (U.2.primeIdealOf ⟨x, hxU'⟩).asIdeal.primeCompl _ hnoeth
  rw [orderAt_eq_idealOrder]
  exact idealOrder_ne_top_of_ne_bot h
end FunctorialResolution.EmbeddedResolution
