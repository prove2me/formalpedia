-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.formallySmooth_sections
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:18:56.499034+00:00
-- url     : https://prove2.me/submissions/a64ebe1a-12b0-407f-9bc2-61fa2ffd75df

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
private theorem formallySmooth_of_ringEquiv (k : Type u) [CommRing k] (R : Type u)
    [CommRing R] [Algebra k R] (e : k ≃+* R) (he : ∀ x : k, e x = algebraMap k R x) :
    Algebra.FormallySmooth k R := by
  have : Algebra.FormallySmooth k k := inferInstance
  exact Algebra.FormallySmooth.of_equiv (AlgEquiv.ofRingEquiv (f := e) (fun x => he x))
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (U : X.Opens)
    (hU : IsAffineOpen U) [Algebra k Γ(X, U)]
    (h : algebraMap k Γ(X, U) = sectionsAlgebraMap k p U) :
    Algebra.FormallySmooth k Γ(X, U) := by
  have hQ : RingHom.Smooth (p.appLE ⊤ U (le_preimage_top k p U)).hom :=
    (AlgebraicGeometry.smooth_iff p).mp ‹AlgebraicGeometry.Smooth p›
      (isAffineOpen_top (Spec (CommRingCat.of k))) hU (le_preimage_top k p U)
  let algSections : Algebra Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U) :=
    (p.appLE ⊤ U (le_preimage_top k p U)).hom.toAlgebra
  have hS : Algebra.Smooth Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U) := hQ
  have : Algebra.FormallySmooth Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U) := hS.formallySmooth
  let algGlobal : Algebra k Γ(Spec (CommRingCat.of k), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toAlgebra
  have : Algebra.FormallySmooth k Γ(Spec (CommRingCat.of k), ⊤) :=
    formallySmooth_of_ringEquiv k Γ(Spec (CommRingCat.of k), ⊤)
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv (fun _ => rfl)
  have : IsScalarTower k Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U) :=
    IsScalarTower.of_algebraMap_eq' (h.trans rfl)
  exact Algebra.FormallySmooth.comp k Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U)
end FunctorialResolution.EmbeddedResolution
