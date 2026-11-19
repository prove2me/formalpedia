-- Prove2me | solution 1 for DiazModulus.dalag_prop_12_13_ii_i
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-18T16:22:29.048226+00:00
-- url     : https://prove2.me/submissions/1d4f3408-54cd-4ac8-87f0-589e00f45cf6

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # DALAG Prop. 12.13, (ii) ⇒ (i)

Assume (ii): for every family `x₁, …, x_n` of elements of `E` such that `1, x₁, …, x_n` are linearly independent
over `k`, the `x_i` are algebraically independent over `k`. Since `1 ∈ E` is non-zero, the singleton `{1}` is a
linearly independent subset of the `k`-vector space `E`, so it extends to a basis `(x_i)_{i ∈ I}` of `E`; the index
set `I` is a subset of `E`, `x_i = i`, and `1 ∈ I` is the distinguished index `i₀`, with `x_{i₀} = 1`. A family is
algebraically independent as soon as each of its finite subfamilies is. A finite set of indices `≠ i₀`, enumerated
as `y₁, …, y_m`, gives a family of elements of `E` such that `1, y₁, …, y_m` is a subfamily of the basis, read in `K`,
with distinct indices: it is linearly independent over `k`. By (ii), `y₁, …, y_m` are algebraically independent over
`k`, and re-indexing along the enumeration gives the finite subfamily. Only finite subfamilies are examined, so `E`
may be infinite-dimensional. -/

universe u v

open DiazModulus in
theorem solution {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (E : Submodule k K) (h1 : (1 : K) ∈ E)
    (hii : ∀ (n : ℕ) (x : Fin n → K), (∀ i, x i ∈ E) →
      LinearIndependent k (Fin.cons (1 : K) x : Fin (n + 1) → K) → AlgebraicIndependent k x) :
    ∃ (ι : Type v) (b : Module.Basis ι k ↥E) (i₀ : ι),
      (b i₀ : K) = 1 ∧ AlgebraicIndependent k (fun i : {i : ι // i ≠ i₀} => (b i : K)) := by
  classical
  have hs : LinearIndepOn k id ({⟨1, h1⟩} : Set ↥E) :=
    LinearIndepOn.singleton (fun h => one_ne_zero (congrArg Subtype.val h))
  have hmem : (⟨1, h1⟩ : ↥E) ∈ hs.extend (Set.subset_univ _) := hs.subset_extend _ rfl
  set b := Module.Basis.extend hs with hb
  set i₀ : ↥(hs.extend (Set.subset_univ _)) := ⟨⟨1, h1⟩, hmem⟩ with hi₀
  refine ⟨_, b, i₀, by simp [hb, hi₀], ?_⟩
  have hbli : LinearIndependent k (fun i => (b i : K)) :=
    b.linearIndependent.map' E.subtype (Submodule.ker_subtype _)
  refine algebraicIndependent_of_finite_type fun t ht => ?_
  have : Finite t := ht.to_subtype
  let e := Finite.equivFin t
  let y : Fin (Nat.card t) → K := fun a => (b (e.symm a).1.1 : K)
  have hinj : Function.Injective
      (Fin.cons i₀ (fun a => (e.symm a).1.1) : Fin (Nat.card t + 1) → _) := by
    rw [Fin.cons_injective_iff]
    refine ⟨?_, ?_⟩
    · rintro ⟨a, ha⟩; exact (e.symm a).1.2 ha
    · intro a a' h; exact e.symm.injective (Subtype.ext (Subtype.ext h))
  have hy : AlgebraicIndependent k y := by
    refine hii _ y (fun a => (b _).2) ?_
    convert hbli.comp _ hinj using 1
    ext j; refine Fin.cases ?_ (fun a => ?_) j
    · simp only [Fin.cons_zero, Function.comp_apply, hb, hi₀, Module.Basis.coe_extend]
    · simp only [Fin.cons_succ, Function.comp_apply, y]
  convert hy.comp e e.injective using 1
  funext z; simp only [y, Function.comp_apply, Equiv.symm_apply_apply]
