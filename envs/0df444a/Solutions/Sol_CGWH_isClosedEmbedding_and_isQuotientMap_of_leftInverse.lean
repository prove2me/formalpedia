-- Prove2me | solution 1 for CGWH.isClosedEmbedding_and_isQuotientMap_of_leftInverse
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:36:27.070671+00:00
-- url     : https://prove2.me/submissions/5db3891d-51c6-4275-b935-c9cb07096f32

import Definitions.Def_CGWH_WeakHausdorff
import Theorems.Thm_CGWH_t2Space_of_surjective_of_compactSpace_t2Space

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace Sol_CGWH_isClosedEmbedding_and_isQuotientMap_of_leftInverse

open CGWH

/-- A subspace of a weakly Hausdorff space is weakly Hausdorff. -/
theorem wh_subtype (X : Type u) [TopologicalSpace X] [WeaklyHausdorffSpace X] (s : Set X) :
    WeaklyHausdorffSpace s := by
  refine ⟨fun K _ _ _ f hf => ?_⟩
  have h := WeaklyHausdorffSpace.isClosed_range K (fun k => (f k : X))
    (continuous_subtype_val.comp hf)
  have : Set.range f = Subtype.val ⁻¹' (Set.range fun k => (f k : X)) := by
    ext y; constructor
    · rintro ⟨k, rfl⟩; exact ⟨k, rfl⟩
    · rintro ⟨k, hk⟩; exact ⟨k, Subtype.ext hk⟩
  rw [this]; exact h.preimage continuous_subtype_val

/-- Two continuous maps from a compact Hausdorff space into a weakly Hausdorff space agree on a
closed set. -/
theorem isClosed_eq_of_wh {K Y : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [TopologicalSpace Y] [WeaklyHausdorffSpace Y] {g1 g2 : K → Y}
    (h1 : Continuous g1) (h2 : Continuous g2) : IsClosed {k | g1 k = g2 k} := by
  let h : K ⊕ K → Y := Sum.elim g1 g2
  have hh : Continuous h := h1.sumElim h2
  haveI : WeaklyHausdorffSpace (Set.range h) := wh_subtype Y _
  let q : K ⊕ K → Set.range h := Set.rangeFactorization h
  have hq : Continuous q := hh.subtype_mk _
  have hs : Function.Surjective q := Set.rangeFactorization_surjective
  haveI : T2Space (Set.range h) := t2Space_of_surjective_of_compactSpace_t2Space hq hs
  have : {k | g1 k = g2 k} = {k | q (Sum.inl k) = q (Sum.inr k)} := by
    ext k; simp [q, h, Subtype.ext_iff, Set.rangeFactorization]
  rw [this]
  exact isClosed_eq (hq.comp continuous_inl) (hq.comp continuous_inr)

/-- The coincidence set of two continuous maps from a compactly generated space into a weakly
Hausdorff space is closed. -/
theorem isClosed_setOf_eq' {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactlyGeneratedSpace X] [WeaklyHausdorffSpace Y] {f g : X → Y}
    (hf : Continuous f) (hg : Continuous g) : IsClosed {x : X | f x = g x} := by
  refine CompactlyGeneratedSpace.isClosed' fun K _ _ _ h hh => ?_
  exact isClosed_eq_of_wh (hf.comp hh) (hg.comp hh)

end Sol_CGWH_isClosedEmbedding_and_isQuotientMap_of_leftInverse

open CGWH

theorem solution
    {X : Type u} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactlyGeneratedSpace X] [WeaklyHausdorffSpace X]
    {g : X → Y} {f : Y → X} (hg : Continuous g) (hf : Continuous f)
    (h : Function.LeftInverse g f) : IsClosedEmbedding f ∧ IsQuotientMap g := by
  refine ⟨⟨Function.LeftInverse.isEmbedding h hg hf, ?_⟩, ?_⟩
  · have hrange : Set.range f = {x | f (g x) = x} := by
      ext x; constructor
      · rintro ⟨y, rfl⟩; simp [h y]
      · intro hx; exact ⟨g x, hx⟩
    rw [hrange]
    exact Sol_CGWH_isClosedEmbedding_and_isQuotientMap_of_leftInverse.isClosed_setOf_eq'
      (hf.comp hg) continuous_id
  · refine IsQuotientMap.of_comp hf hg ?_
    rw [h.comp_eq_id]; exact IsQuotientMap.id
