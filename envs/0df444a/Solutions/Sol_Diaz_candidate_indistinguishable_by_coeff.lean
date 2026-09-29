-- Prove2me | solution 1 for Diaz.candidate_indistinguishable_by_coeff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:34:06.872993+00:00
-- url     : https://prove2.me/submissions/311d5009-a6a8-4177-bf0f-b1fc20fc77e1

/-
# Corollary `cor:transfer` in full, and the consequence its prose asserts

Source: Carlo Perassi's note `query_note_2.tex`, Corollary 7 (`cor:transfer`)
and the paragraph immediately following it.  The mathematics is his and
predates this mission; no novelty is claimed here.  The contribution is the
formalisation.

## What is already on the platform, and what is not

* `Diaz.coeff_transfer` (uuid `bac62a30-…`, **Proved**) is the *forward
  identity* half of the corollary, over an arbitrary subfield `K` with
  `Fin m` / `Fin n` index types:
  `Φ (∑ i, ∑ j, w i * M i j * v j) = ∑ i, ∑ j, w i * Φ (M i j) * v j`.
  It does **not** carry the corollary's "consequently" clause.
* `Diaz.candidate_no_vanishing_coeff_Qbar` (uuid `16400e12-…`, **Proved**) is
  the specialised non-vanishing statement for the single `2 x 2` matrix
  `Hmat u r` with `Fin 2` coefficient vectors.

Missing, and supplied below:

1. `Diaz.coeff_transfer_iff` — the corollary as stated, both clauses, with
   arbitrary finite index types.  The equivalence is the half that needs
   injectivity of `Φ`, which is what the note's proof invokes.
2. `Diaz.candidate_indistinguishable_by_coeff` — the sentence the note's prose
   asserts and does not formalise: no vanishing statement with algebraic
   coefficients, about a matrix over `Q̄(u)`, distinguishes a candidate from an
   ordinary point of the same circle.

The file's preamble is that of `Diaz.candidate_indistinguishable`, the widest
of the two target preambles; the per-node preambles are recorded in the
publish payload.
-/
import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation
import Theorems.Thm_Diaz_candidate_indistinguishable

open ComplexConjugate
open Diaz

/-! ## Node 1: the corollary, in full

Statement shape.  The base is an arbitrary subfield `K ⊆ ℂ`, matching the
generality of the existing `Diaz.coeff_transfer`; the intended `K` is `Qbar`.
Index types are arbitrary `Fintype`s rather than `Fin m` / `Fin n`: `wᵀ M v` is
a finite double sum, so finiteness is what the expression *means*, not an extra
hypothesis, and there is no reason to force the caller through a numbering of
the index set.  `M` is an arbitrary complex matrix — the note constrains only
`w` and `v` to be algebraic, and nothing more is needed. -/

/-- **Corollary `cor:transfer` (Carlo Perassi, `query_note_2.tex`).**  A ring
homomorphism `Φ : ℂ → ℂ` fixing a subfield `K` pointwise commutes with the
formation of matrix coefficients `wᵀ M v` whose coefficient vectors lie in `K`,
and — being injective, as any ring homomorphism out of a field is — detects
their vanishing exactly. -/
theorem Diaz.coeff_transfer_iff {K : Subfield ℂ} {m n : Type*} [Fintype m] [Fintype n]
    (Φ : ℂ →+* ℂ) (hK : ∀ a ∈ K, Φ a = a)
    (M : Matrix m n ℂ) (w : m → ℂ) (v : n → ℂ)
    (hw : ∀ i, w i ∈ K) (hv : ∀ j, v j ∈ K) :
    Φ (∑ i, ∑ j, w i * M i j * v j) = ∑ i, ∑ j, w i * Φ (M i j) * v j ∧
      ((∑ i, ∑ j, w i * M i j * v j) = 0 ↔ (∑ i, ∑ j, w i * Φ (M i j) * v j) = 0) := by
  have key : Φ (∑ i, ∑ j, w i * M i j * v j) = ∑ i, ∑ j, w i * Φ (M i j) * v j := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, hK _ (hw i), hK _ (hv j)]
  refine ⟨key, ?_, ?_⟩
  · intro h0
    rw [← key, h0, map_zero]
  · intro h0
    refine Φ.injective ?_
    rw [key, h0, map_zero]

/-! ## Imported platform node (stub)

`Diaz.candidate_indistinguishable`, uuid `3592d95c-2f6b-4a36-9888-290e1e3a2c0e`,
status **Proved** on the platform.  Its statement is reproduced verbatim as a
`sorry`-carrying stub, exactly as the `Theorems/Thm_*.lean` convention does,
because this exercise is confined to a single file.  This is the only `sorry`
in the file; the `sorryAx` in the axiom report for node 2 comes from it and
from nowhere else. -/

/-! ### Two facts about `hull`, unfolded from its definition -/

namespace Diaz

theorem self_mem_hull (K : Subfield ℂ) (x : ℂ) : x ∈ hull K x :=
  Subfield.subset_closure (Set.mem_union_right _ rfl)

theorem base_mem_hull (K : Subfield ℂ) (x : ℂ) {a : ℂ} (ha : a ∈ K) : a ∈ hull K x :=
  Subfield.subset_closure (Set.mem_union_left _ ha)

end Diaz

/-! ## Node 2: the consequence the note's prose asserts

"For `M` with entries in `Q̄(u)`, the entries of `Φ(M)` are the same expressions
with `t` in place of `u`, by (a), (b), (c); so a vanishing statement about
coefficients over `Q̄` holds for the candidate iff it holds for `t`; no such
statement distinguishes a candidate from an ordinary point of the circle."

"The same expressions with `t` in place of `u`" is rendered by the clauses that
pin `Φ` down on `Q̄(u)` — it fixes `Q̄`, sends `u` to `t`, commutes with
conjugation there (`Diaz.eqOn_hull` says these determine it on `Q̄(u)`) —
together with the clause saying it lands in `Q̄(t)`.

Note also that `t * conj t = r ^ 2` is recovered here.  The note's Theorem 6
states it, but the platform node `Diaz.candidate_indistinguishable` does not;
it follows from the clauses that node does carry, by applying `Φ` to
`u * conj u = r ^ 2`.  Without it the statement below could not say "the same
circle". -/

/-- **No vanishing statement with algebraic coefficients distinguishes a
candidate from an ordinary point of the same circle.**

Let `u` be a candidate: `u ≠ 0`, `exp u` algebraic over `ℚ`, and
`u * conj u = r ^ 2` for a non-zero real algebraic `r`.  Then there are a point
`t` of the same circle — non-zero, transcendental over `Q̄`, with
`t * conj t = r ^ 2` — and a ring homomorphism `Φ : ℂ → ℂ` which fixes `Q̄`
pointwise, sends `u` to `t`, and commutes with complex conjugation on `Q̄(u)`,
such that `Φ` carries `Q̄(u)` into `Q̄(t)` and, for every matrix `M` over
`Q̄(u)` and all coefficient vectors `w`, `v` over `Q̄`, the transported matrix
`Φ(M)` is again over `Q̄(t)` and

  `wᵀ M v = 0  ↔  wᵀ Φ(M) v = 0`.

The mathematics is Carlo Perassi's, from a note predating this mission
(Corollary `cor:transfer` and the paragraph following it); no novelty is
claimed for it here. -/
theorem solution
    {u r : ℂ} (hu0 : u ≠ 0) (hexp : IsAlgebraic ℚ (Complex.exp u))
    (hr : r ∈ Qbar) (hrr : conj r = r) (hr0 : r ≠ 0)
    (h : u * conj u = r ^ 2) :
    ∃ t : ℂ, t ≠ 0 ∧ Transcendental (↥Qbar) t ∧ t * conj t = r ^ 2 ∧
      ∃ Φ : ℂ →+* ℂ, (∀ a ∈ Qbar, Φ a = a) ∧ Φ u = t ∧
        (∀ z ∈ hull Qbar u, Φ (conj z) = conj (Φ z)) ∧
        (∀ z ∈ hull Qbar u, Φ z ∈ hull Qbar t) ∧
        ∀ (p q : ℕ) (M : Matrix (Fin p) (Fin q) ℂ) (w : Fin p → ℂ) (v : Fin q → ℂ),
          (∀ i j, M i j ∈ hull Qbar u) → (∀ i, w i ∈ Qbar) → (∀ j, v j ∈ Qbar) →
            (∀ i j, Φ (M i j) ∈ hull Qbar t) ∧
              ((∑ i, ∑ j, w i * M i j * v j) = 0 ↔
                (∑ i, ∑ j, w i * Φ (M i j) * v j) = 0) := by
  classical
  obtain ⟨t, ht0, httr, Φ, hfix, hΦu, hconj⟩ :=
    Diaz.candidate_indistinguishable hu0 hexp hr hrr hr0 h
  -- `Φ` carries `Q̄(u)` into `Q̄(t)`: the preimage of `Q̄(t)` is a subfield
  -- containing `Q̄` and `u`, and `Q̄(u)` is the smallest such.
  have hmap : ∀ z ∈ hull Qbar u, Φ z ∈ hull Qbar t := by
    have hle : hull Qbar u ≤ Subfield.comap Φ (hull Qbar t) := by
      show Subfield.closure ((Qbar : Set ℂ) ∪ {u}) ≤ _
      rw [Subfield.closure_le]
      rintro x (hx | rfl)
      · show Φ x ∈ hull Qbar t
        rw [hfix x hx]
        exact Diaz.base_mem_hull Qbar t hx
      · show Φ x ∈ hull Qbar t
        rw [hΦu]
        exact Diaz.self_mem_hull Qbar t
    exact fun z hz => hle hz
  refine ⟨t, ht0, httr, ?_, Φ, hfix, hΦu, hconj, hmap, ?_⟩
  · -- `t` lies on the same circle: apply `Φ` to `u * conj u = r ^ 2`.
    have hru : Φ (u * conj u) = r ^ 2 := by
      rw [h]
      exact hfix _ (pow_mem hr 2)
    rw [map_mul, hconj u (Diaz.self_mem_hull Qbar u), hΦu] at hru
    exact hru
  · intro p q M w v hM hw hv
    exact ⟨fun i j => hmap _ (hM i j),
      (Diaz.coeff_transfer_iff Φ hfix M w v hw hv).2⟩
