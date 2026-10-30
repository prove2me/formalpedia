-- Prove2me | solution 1 for DiazModulus.exists_boxHilb_family
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T08:06:48.609295+00:00
-- url     : https://prove2.me/submissions/8d4a4536-0215-4c4d-80d3-d495dcfbe344

import Mathlib
import Definitions.Def_DiazHilbertBox

open Complex ComplexConjugate

/-! # A family realising the box Hilbert function

There are `h_I(T)` elements of `F_T`, linearly independent modulo `I`, that span `F_T` modulo
`I` (the family `E` of DALAG p. 245).

Write `q : S → S ⧸ I` for the quotient map and `W = q(F_T)`, so `h_I(T) = dim_K W`. Take a basis
`b` of `W` indexed by `Fin h_I(T)` (`Module.finBasis`) and lift each `b_i` to some `e_i ∈ F_T`
with `q(e_i) = b_i`. Then `q ∘ e` is `b` followed by the inclusion of `W`, hence independent.
For spanning, `q(span e) = span (q ∘ e) = W` (`Submodule.map_span`, and `b` spans `W`), so for
`x ∈ F_T` some `y ∈ span e` has `q y = q x`, that is `x - y ∈ I` (`Ideal.Quotient.eq`). -/

namespace C11_F4
open DiazModulus
end C11_F4

open DiazModulus C11_F4 in
theorem solution {K S B : Type*} [Field K] [CommRing S] [Algebra K S] (F : (B → ℕ) → Submodule K S)
    (hFfin : ∀ Tₑ, FiniteDimensional K ↥(F Tₑ)) (I : Ideal S) (T : B → ℕ) :
    ∃ e : Fin (boxHilb F I T) → S, (∀ i, e i ∈ F T) ∧
      LinearIndependent K (fun i => Ideal.Quotient.mk I (e i)) ∧
      ∀ x ∈ F T, ∃ y ∈ Submodule.span K (Set.range e), x - y ∈ I := by
  set q := (Ideal.Quotient.mkₐ K I).toLinearMap
  set W := (F T).map q
  let b : Module.Basis (Fin (boxHilb F I T)) K W := Module.finBasis K W
  have hlift : ∀ i, ∃ s ∈ F T, q s = (b i : S ⧸ I) := fun i => (b i).2
  choose e he hqe using hlift
  have hcomp : (fun i => Ideal.Quotient.mk I (e i)) = W.subtype ∘ b := by
    funext i
    exact hqe i
  refine ⟨e, he, ?_, ?_⟩
  · rw [hcomp]
    exact b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  · intro x hx
    have hspan : (Submodule.span K (Set.range e)).map q = W := by
      rw [Submodule.map_span, ← Set.range_comp]
      change Submodule.span K (Set.range (fun i => Ideal.Quotient.mk I (e i))) = W
      rw [hcomp, Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top,
        Submodule.range_subtype]
    have hqx : q x ∈ (Submodule.span K (Set.range e)).map q := by
      rw [hspan]
      exact Submodule.mem_map_of_mem hx
    obtain ⟨y, hy, hqy⟩ := hqx
    refine ⟨y, hy, ?_⟩
    have : Ideal.Quotient.mk I y = Ideal.Quotient.mk I x := hqy
    rw [Ideal.Quotient.eq] at this
    simpa using I.neg_mem_iff.mpr this
