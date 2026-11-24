-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.JacobianCriterion.formallyEtale_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:01:29.253403+00:00
-- url     : https://prove2.me/submissions/472d3b41-97f9-4e21-b8c3-7e234ece5b24

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_JacobianCriterion
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_formallyUnramified_of_mapBaseChange_surjective
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_mapBaseChange_bijective_of_basis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.JacobianCriterion
variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]
variable [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
namespace FunctorialResolution.EmbeddedResolution.JacobianCriterion
theorem _root_.solution [Algebra.FormallySmooth k S]
    (b : Module.Basis ι S (KaehlerDifferential k S))
    (hb : ∀ i : ι, b i = KaehlerDifferential.D k S (coord k ι S i)) :
    Algebra.FormallyEtale (MvPolynomial ι k) S := by
  have hbij := mapBaseChange_bijective_of_basis k ι S b hb
  have hfu : Algebra.FormallyUnramified (MvPolynomial ι k) S :=
    formallyUnramified_of_mapBaseChange_surjective k ι S hbij.2
  have hh1 : Subsingleton (Algebra.H1Cotangent (MvPolynomial ι k) S) := by
    have key : ∀ z : Algebra.H1Cotangent (MvPolynomial ι k) S, z = 0 := by
      intro z
      have hz : Algebra.H1Cotangent.δ k (MvPolynomial ι k) S z = 0 := by
        have h0 := (Algebra.H1Cotangent.exact_δ_mapBaseChange k (MvPolynomial ι k)
          S).apply_apply_eq_zero z
        refine hbij.1 ?_
        rw [h0, map_zero]
      obtain ⟨w, hw⟩ := (Algebra.H1Cotangent.exact_map_δ k (MvPolynomial ι k) S z).mp hz
      rw [← hw, Subsingleton.elim w 0, map_zero]
    exact ⟨fun x y => by rw [key x, key y]⟩
  refine ⟨?_, ?_⟩
  · infer_instance
  · infer_instance
end FunctorialResolution.EmbeddedResolution.JacobianCriterion
