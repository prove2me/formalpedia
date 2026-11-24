-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isNoetherianRing_stalk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:18:52.116931+00:00
-- url     : https://prove2.me/submissions/92b4c3b7-faa2-4a8c-92b1-11eb08e94f75

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_LocalParameters
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace FunctorialResolution.EmbeddedResolution
private theorem isNoetherianRing_sections_of_smooth (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (U : X.Opens)
    (hU : IsAffineOpen U) : IsNoetherianRing Γ(X, U) := by
  have : IsNoetherianRing k := inferInstance
  have hQ : RingHom.Smooth (p.appLE ⊤ U (le_preimage_top k p U)).hom :=
    (AlgebraicGeometry.smooth_iff p).mp ‹AlgebraicGeometry.Smooth p›
      (isAffineOpen_top (Spec (CommRingCat.of k))) hU (le_preimage_top k p U)
  let algSections : Algebra Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U) :=
    (p.appLE ⊤ U (le_preimage_top k p U)).hom.toAlgebra
  have hS : Algebra.Smooth Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U) := hQ
  have e : k ≃+* Γ(Spec (CommRingCat.of k), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  have : IsNoetherianRing Γ(Spec (CommRingCat.of k), ⊤) :=
    isNoetherianRing_of_surjective k (↥Γ(Spec (CommRingCat.of k), ⊤)) e.toRingHom e.surjective
  obtain ⟨n, f, hf, -⟩ := hS.finitePresentation
  exact isNoetherianRing_of_surjective
    (MvPolynomial (Fin n) (↥Γ(Spec (CommRingCat.of k), ⊤))) (↥Γ(X, U)) f.toRingHom hf
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (x : X) :
    IsNoetherianRing (X.presheaf.stalk x) := by
  have : IsLocallyNoetherian X := ⟨fun U => isNoetherianRing_sections_of_smooth k p U.1 U.2⟩
  infer_instance
end FunctorialResolution.EmbeddedResolution
