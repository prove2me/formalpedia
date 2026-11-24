-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.span_singleton_prod_eq_biInf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:50:12.683808+00:00
-- url     : https://prove2.me/submissions/adaf951d-9e02-424e-b57b-2cc53b2d5023

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace FunctorialResolution.EmbeddedResolution
private theorem prod_notMem_of_isPrime {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    {I : Ideal R} (hI : I.IsPrime) (g : ι → R) (t : Finset ι) :
    (∀ j ∈ t, g j ∉ I) → ∏ j ∈ t, g j ∉ I := by
  induction t using Finset.induction_on with
  | empty =>
      intro _ h1
      rw [Finset.prod_empty] at h1
      refine hI.ne_top ?_
      rw [Ideal.eq_top_iff_one]
      exact h1
  | @insert a u ha ih =>
      intro h hmem
      rw [Finset.prod_insert ha] at hmem
      rcases hI.mem_or_mem hmem with h1 | h1
      · exact h a (Finset.mem_insert_self a u) h1
      · exact ih (fun j hj => h j (Finset.mem_insert_of_mem hj)) h1
private theorem span_singleton_mul_eq_inf {R : Type*} [CommRing R] {a b : R}
    (hpa : (Ideal.span ({a} : Set R)).IsPrime) (hb : b ∉ Ideal.span ({a} : Set R)) :
    Ideal.span ({a * b} : Set R) = Ideal.span ({a} : Set R) ⊓ Ideal.span ({b} : Set R) := by
  refine le_antisymm (le_inf ?_ ?_) ?_
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_span_singleton.mpr ⟨b, rfl⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_span_singleton.mpr ⟨a, mul_comm a b⟩
  · intro z hz
    rw [Submodule.mem_inf] at hz
    obtain ⟨hz1, hz2⟩ := hz
    obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton.mp hz2
    have hv : v ∈ Ideal.span ({a} : Set R) := (hpa.mem_or_mem hz1).resolve_left hb
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton.mp hv
    exact Ideal.mem_span_singleton.mpr ⟨w, by ring⟩
end FunctorialResolution.EmbeddedResolution
namespace IsLocalization
end IsLocalization
namespace Ideal
end Ideal
namespace KaehlerDifferential
end KaehlerDifferential
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    (f : ι → R) (s : Finset ι)
    (hp : ∀ i ∈ s, (Ideal.span ({f i} : Set R)).IsPrime)
    (hdvd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f j ∉ Ideal.span ({f i} : Set R)) :
    Ideal.span ({∏ i ∈ s, f i} : Set R) = ⨅ i ∈ s, Ideal.span ({f i} : Set R) := by
  revert hp hdvd
  induction s using Finset.induction_on with
  | empty =>
      intro _ _
      simp
  | @insert a u ha ih =>
      intro hp hdvd
      have hpa : (Ideal.span ({f a} : Set R)).IsPrime := hp a (Finset.mem_insert_self a u)
      have hP : (∏ i ∈ u, f i) ∉ Ideal.span ({f a} : Set R) := by
        refine prod_notMem_of_isPrime hpa f u ?_
        intro j hj
        exact hdvd a (Finset.mem_insert_self a u) j (Finset.mem_insert_of_mem hj)
          (by rintro rfl; exact ha hj)
      have ihu := ih (fun i hi => hp i (Finset.mem_insert_of_mem hi))
        (fun i hi j hj hij =>
          hdvd i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)
      rw [Finset.prod_insert ha, span_singleton_mul_eq_inf hpa hP, ihu, Finset.iInf_insert]
end FunctorialResolution.EmbeddedResolution
