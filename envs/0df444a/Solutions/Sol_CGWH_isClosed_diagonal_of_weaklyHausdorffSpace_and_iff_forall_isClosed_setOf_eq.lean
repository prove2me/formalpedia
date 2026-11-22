-- Prove2me | solution 1 for CGWH.isClosed_diagonal_of_weaklyHausdorffSpace_and_iff_forall_isClosed_setOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:32:39.093393+00:00
-- url     : https://prove2.me/submissions/c7b3a1bf-dcc4-4e7d-b047-c034eeecc5be

import Definitions.Def_CGWH_WeakHausdorff
import Theorems.Thm_CGWH_t2Space_of_surjective_of_compactSpace_t2Space

open Topology TopologicalSpace

set_option autoImplicit false

universe u

open CGWH

namespace Sol_CGWH_isClosed_diagonal_of_weaklyHausdorffSpace_and_iff_forall_isClosed_setOf_eq

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

/-- Closed sets of the `k`-ification: preimages under all test maps are closed. -/
theorem isClosed_cg_iff {X : Type u} [TopologicalSpace X] (s : Set X) :
    IsClosed[TopologicalSpace.compactlyGenerated.{u} X] s ↔
      ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K] (f : K → X),
        Continuous f → IsClosed (f ⁻¹' s) := by
  simp only [TopologicalSpace.compactlyGenerated, isClosed_coinduced, isClosed_sigma_iff,
    Sigma.forall]
  constructor
  · intro h K _ _ _ f hf; exact h (CompHaus.of K) ⟨f, hf⟩
  · intro h S f; exact h S f f.2

/-- Two test maps into a weakly Hausdorff space agree on a closed set. -/
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

end Sol_CGWH_isClosed_diagonal_of_weaklyHausdorffSpace_and_iff_forall_isClosed_setOf_eq

open Sol_CGWH_isClosed_diagonal_of_weaklyHausdorffSpace_and_iff_forall_isClosed_setOf_eq

theorem solution (X : Type u) [TopologicalSpace X] :
    (WeaklyHausdorffSpace X →
        IsClosed[TopologicalSpace.compactlyGenerated.{u} (X × X)] (Set.diagonal X)) ∧
      (IsClosed[TopologicalSpace.compactlyGenerated.{u} (X × X)] (Set.diagonal X) ↔
        ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K] (g : K → X),
          Continuous g → IsClosed {p : K × K | g p.1 = g p.2}) := by
  refine ⟨fun hX => ?_, ?_, ?_⟩
  · rw [isClosed_cg_iff]
    intro K _ _ _ f hf
    exact isClosed_eq_of_wh (continuous_fst.comp hf) (continuous_snd.comp hf)
  · intro h K _ _ _ g hg
    rw [isClosed_cg_iff] at h
    exact h (K × K) (fun p => (g p.1, g p.2)) (by fun_prop)
  · intro h
    rw [isClosed_cg_iff]
    intro K _ _ _ f hf
    have h1 : Continuous (fun k => (f k).1) := continuous_fst.comp hf
    have h2 : Continuous (fun k => (f k).2) := continuous_snd.comp hf
    have := h (K ⊕ K) (Sum.elim (fun k => (f k).1) (fun k => (f k).2)) (h1.sumElim h2)
    have h3 := this.preimage (f := fun k : K => ((Sum.inl k : K ⊕ K), (Sum.inr k : K ⊕ K)))
      (by fun_prop)
    exact h3
