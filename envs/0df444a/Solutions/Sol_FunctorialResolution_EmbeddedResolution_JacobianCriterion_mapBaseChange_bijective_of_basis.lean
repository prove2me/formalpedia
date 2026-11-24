-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.JacobianCriterion.mapBaseChange_bijective_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:47:38.67719+00:00
-- url     : https://prove2.me/submissions/e24cb250-dfc7-401e-bc1d-2ad52157a441

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_JacobianCriterion
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_tensorKaehlerBasis_mapBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.JacobianCriterion.tensorKaehlerBasis_mapBaseChange

set_option autoImplicit false
open scoped TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.JacobianCriterion
variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]
variable [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
namespace FunctorialResolution.EmbeddedResolution.JacobianCriterion
theorem _root_.solution
    (b : Module.Basis ι S (KaehlerDifferential k S))
    (hb : ∀ i : ι, b i = KaehlerDifferential.D k S (coord k ι S i)) :
    Function.Bijective (KaehlerDifferential.mapBaseChange k (MvPolynomial ι k) S) := by
  have h : (KaehlerDifferential.mapBaseChange k (MvPolynomial ι k) S) =
      (((tensorKaehlerBasis k ι S).equiv b (Equiv.refl ι)) :
        (S ⊗[MvPolynomial ι k] KaehlerDifferential k (MvPolynomial ι k)) →ₗ[S]
          KaehlerDifferential k S) := by
    refine (tensorKaehlerBasis k ι S).ext fun i => ?_
    rw [tensorKaehlerBasis_mapBaseChange]
    simp [hb i]
  have hx : ∀ x, KaehlerDifferential.mapBaseChange k (MvPolynomial ι k) S x =
      ((tensorKaehlerBasis k ι S).equiv b (Equiv.refl ι)) x := by
    intro x
    have h2 := congrArg
      (fun f : (S ⊗[MvPolynomial ι k] KaehlerDifferential k (MvPolynomial ι k)) →ₗ[S]
        KaehlerDifferential k S => f x) h
    simpa using h2
  constructor
  · intro x y hxy
    apply ((tensorKaehlerBasis k ι S).equiv b (Equiv.refl ι)).injective
    rw [← hx, ← hx, hxy]
  · intro y
    obtain ⟨x, hxe⟩ := ((tensorKaehlerBasis k ι S).equiv b (Equiv.refl ι)).surjective y
    exact ⟨x, (hx x).trans hxe⟩
end FunctorialResolution.EmbeddedResolution.JacobianCriterion
