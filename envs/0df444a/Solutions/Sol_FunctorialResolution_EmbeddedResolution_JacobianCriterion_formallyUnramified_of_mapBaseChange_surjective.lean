-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.JacobianCriterion.formallyUnramified_of_mapBaseChange_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:47:37.755554+00:00
-- url     : https://prove2.me/submissions/d7d76201-e518-4344-979b-e213086a3085

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
    (h : Function.Surjective (KaehlerDifferential.mapBaseChange k (MvPolynomial ι k) S)) :
    Algebra.FormallyUnramified (MvPolynomial ι k) S := by
  have hexact := KaehlerDifferential.exact_mapBaseChange_map k (MvPolynomial ι k) S
  have hD : ∀ s : S, KaehlerDifferential.D (MvPolynomial ι k) S s = 0 := by
    intro s
    obtain ⟨y, hy⟩ := h (KaehlerDifferential.D k S s)
    have h2 := hexact.apply_apply_eq_zero y
    rw [hy, KaehlerDifferential.map_D] at h2
    simpa using h2
  have key : ∀ x : KaehlerDifferential (MvPolynomial ι k) S, x = 0 := by
    intro x
    have hx : x ∈ Submodule.span S
        (Set.range (KaehlerDifferential.D (MvPolynomial ι k) S)) := by
      rw [KaehlerDifferential.span_range_derivation]
      exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨s, rfl⟩ := hy
        exact hD s
    | zero => rfl
    | add a b _ _ ha hb => rw [ha, hb, add_zero]
    | smul c a _ ha => rw [ha, smul_zero]
  exact Algebra.FormallyUnramified.mk ⟨fun a b => by rw [key a, key b]⟩
end FunctorialResolution.EmbeddedResolution.JacobianCriterion
