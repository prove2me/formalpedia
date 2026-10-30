-- Prove2me | solution 1 for DiazModulus.exists_mem_forall_notMem_of_not_subset
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T08:23:26.245367+00:00
-- url     : https://prove2.me/submissions/e1c023db-2867-44f7-839f-d2d4e5866047

import Mathlib

open Complex ComplexConjugate

/-! # Prime avoidance for a subspace over an infinite field

Let `K` be an infinite field, `S` a `K`-algebra, `V` a `K`-subspace of `S` and `P` a finite set of
ideals of `S`, none of which contains `V`. For each `p ∈ P`, the trace `V ∩ p` is a `K`-subspace of
`V` (the preimage of `p`, viewed as a `K`-subspace of `S`, under the inclusion `V → S`), and it is a
proper subspace because `V ⊄ p`. A vector space over an infinite field is never a finite union of
proper subspaces (Mathlib's `Subspace.biUnion_ne_univ_of_top_notMem`), so some `x ∈ V` lies in no
`V ∩ p`, that is, in no `p ∈ P`. No primality is needed. -/

namespace C11_R3a

/-- The trace of an ideal `p` on the `K`-subspace `V`, as a `K`-subspace of `V`. -/
noncomputable abbrev trace {K S : Type*} [Field K] [CommRing S] [Algebra K S]
    (V : Submodule K S) (p : Ideal S) : Submodule K V :=
  (p.restrictScalars K).comap V.subtype

theorem trace_ne_top {K S : Type*} [Field K] [CommRing S] [Algebra K S]
    (V : Submodule K S) (p : Ideal S) (h : ¬ (V : Set S) ⊆ (p : Set S)) :
    trace V p ≠ ⊤ := by
  intro htop
  apply h
  intro x hx
  have : (⟨x, hx⟩ : V) ∈ trace V p := htop ▸ Submodule.mem_top
  exact this

end C11_R3a

open C11_R3a in
theorem solution {K S : Type*} [Field K] [CommRing S] [Algebra K S] [Infinite K]
    (V : Submodule K S) (P : Set (Ideal S)) (hP : P.Finite)
    (hV : ∀ p ∈ P, ¬ (V : Set S) ⊆ (p : Set S)) :
    ∃ x ∈ V, ∀ p ∈ P, x ∉ p := by
  classical
  set s : Finset (Submodule K V) := hP.toFinset.image (trace V) with hs
  have htop : (⊤ : Submodule K V) ∉ s := by
    intro hmem
    obtain ⟨p, hp, hpt⟩ := Finset.mem_image.mp hmem
    exact trace_ne_top V p (hV p (hP.mem_toFinset.mp hp)) hpt
  have hne := Subspace.biUnion_ne_univ_of_top_notMem (E := V) htop
  obtain ⟨v, hv⟩ : ∃ v : V, v ∉ ⋃ q ∈ s, (q : Set V) := by
    by_contra hcon
    exact hne (Set.eq_univ_of_forall fun v => not_not.mp fun hv => hcon ⟨v, hv⟩)
  refine ⟨v, v.2, fun p hp hvp => hv ?_⟩
  refine Set.mem_biUnion (x := trace V p) ?_ ?_
  · exact Finset.mem_image.mpr ⟨p, hP.mem_toFinset.mpr hp, rfl⟩
  · exact hvp
