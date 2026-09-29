-- Prove2me | solution 2 for Diaz.candidate_indistinguishable_by_coeff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:21:01.79386+00:00
-- url     : https://prove2.me/submissions/f4953c8f-bdaa-4324-9681-ef7368be9fb7

/-
`Diaz.candidate_indistinguishable_by_coeff`, reproved so that it uses the
platform nodes it depends on rather than an inlined copy of one of them.

The original submission had to inline `Diaz.coeff_transfer_iff`, which was
published in the same batch and so was not yet importable.  It now is, and the
proof below is the composition of two published nodes:

  * `Diaz.candidate_indistinguishable` supplies the point `t` and the ring
    homomorphism `Φ`;
  * `Diaz.coeff_transfer_iff` supplies the "consequently" clause of the note's
    Corollary `cor:transfer`, that `Φ` detects the vanishing of a matrix
    coefficient with algebraic coefficient vectors exactly.

The mathematics is Carlo Perassi's, from a note predating this mission; no
novelty is claimed for it here.  Only the routing has changed.
-/
import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation
import Theorems.Thm_Diaz_candidate_indistinguishable
import Theorems.Thm_Diaz_coeff_transfer_iff

open ComplexConjugate
open Diaz

/-! ## Imported platform nodes

`Diaz.candidate_indistinguishable` (uuid `3592d95c-…`) and
`Diaz.coeff_transfer_iff` (uuid `86f5de0a-…`), both **Proved**, are imported
from `Theorems/`.  Nothing about either is restated here. -/

/-! ### Two facts about `hull`, unfolded from its definition -/

namespace Diaz

theorem self_mem_hull (K : Subfield ℂ) (x : ℂ) : x ∈ hull K x :=
  Subfield.subset_closure (Set.mem_union_right _ rfl)

theorem base_mem_hull (K : Subfield ℂ) (x : ℂ) {a : ℂ} (ha : a ∈ K) : a ∈ hull K x :=
  Subfield.subset_closure (Set.mem_union_left _ ha)

end Diaz

/-! ## The consequence the note's prose asserts

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
