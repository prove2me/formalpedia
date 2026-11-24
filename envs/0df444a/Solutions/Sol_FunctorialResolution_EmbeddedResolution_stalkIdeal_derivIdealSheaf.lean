-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.stalkIdeal_derivIdealSheaf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:16:54.848893+00:00
-- url     : https://prove2.me/submissions/05b46dc6-c62e-4a50-b26d-5d9742281580

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_LocalParameters
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isScalarTower_stalk
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_bot
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_map_derivIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_eq_map_germ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal



set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (x : X) :
    stalkIdeal (derivIdealSheaf k p I) x =
      @derivIdeal k _ _ _ (stalkAlgebra k p x) (stalkIdeal I x) := by
  rcases isEmpty_or_nonempty {U : X.affineOpens // x ∈ U.1.1} with hE | ⟨⟨U, hx⟩⟩
  · have h1 : ∀ J : X.IdealSheafData, stalkIdeal J x = ⊥ := fun J =>
      iSup_of_empty (fun U : {U : X.affineOpens // x ∈ U.1.1} =>
        Ideal.map (X.presheaf.germ U.1.1 x U.2).hom (J.ideal U.1))
    rw [h1 (derivIdealSheaf k p I), h1 I]
    exact (@derivIdeal_bot k _ _ _ (stalkAlgebra k p x)).symm
  · have hU : IsAffineOpen U.1 := U.2
    let algk : Algebra k Γ(X, U.1) := sectionsAlgebra k p U.1
    let algst : Algebra k (X.presheaf.stalk x) := stalkAlgebra k p x
    let algS : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
      (X.presheaf.germ U.1 x hx).hom.toAlgebra
    have : IsScalarTower k Γ(X, U.1) (X.presheaf.stalk x) :=
      isScalarTower_stalk k p U.1 x hx rfl rfl rfl
    have : Module.FinitePresentation Γ(X, U.1) (KaehlerDifferential k Γ(X, U.1)) :=
      finitePresentation_kaehlerDifferential_sections k p U rfl
    have _hloc : IsLocalization (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
        (X.presheaf.stalk x) := hU.isLocalization_stalk ⟨x, hx⟩
    rw [stalkIdeal_eq_map_germ (derivIdealSheaf k p I) x U hx,
      stalkIdeal_eq_map_germ I x U hx, derivIdealSheaf_ideal]
    exact map_derivIdeal (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (I.ideal U)
end FunctorialResolution.EmbeddedResolution
