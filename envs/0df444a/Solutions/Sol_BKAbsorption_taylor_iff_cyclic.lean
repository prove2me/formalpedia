-- Prove2me | solution 1 for BKAbsorption.taylor_iff_cyclic
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-07T17:40:59.637844+00:00
-- url     : https://prove2.me/submissions/d3546046-a436-4105-8bf7-3ecc7abea10c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_BKAbsorption_defs
import Theorems.Thm_BKAbsorption_cyclic_term_prime
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Algebra.Group.Fin.Basic

/-!
Barto–Kozik, Theorem 4.1, reduced to Theorem 4.2 (`BKAbsorption.cyclic_term_prime`, imported as a
platform theorem), exactly as in the paper: a cyclic term of arity `k ≥ 2` is a Taylor term, and
there are primes `p > |A|`.
-/

universe u₁ v₁ w₁

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

namespace BKAbsorption

namespace T41

variable {L : FirstOrder.Language.{u₁, v₁}} {A : Type w₁} [L.Structure A]

/-- A cyclic term operation of arity `k ≥ 2` is a Taylor term: for the identity at position
`j`, take `x` at `j` on the left and `x` at `j + 1` on the right; they differ by one cyclic
shift. -/
theorem taylor_of_cyclic (hid : IsIdempotent L A) {k : ℕ} (hk : 2 ≤ k)
    (h : HasCyclicTermOp L A k) : ∃ T : TaylorDatum L, IsTaylorAlg T A := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 + 1 := ⟨k - 2, by omega⟩
  obtain ⟨t, -, ht⟩ := h
  refine ⟨TaylorDatum.mk (m + 1 + 1) t (fun j i => decide (i ≠ j))
      (fun j i => decide (i ≠ j + 1)) ?_ ?_, hid, ?_⟩
  · intro j; simp
  · intro j; simp
  · intro j x y
    show t.realize (fun i => cond (decide (i ≠ j)) y x) =
      t.realize (fun i => cond (decide (i ≠ j + 1)) y x)
    rw [ht (fun i => cond (decide (i ≠ j + 1)) y x)]
    congr 1
    funext i
    simp only [Function.comp_apply, finRotate_succ_apply, ne_eq, add_left_inj]

theorem main [L.IsAlgebraic] [Finite A] (hid : IsIdempotent L A) :
    ((∃ T : TaylorDatum L, IsTaylorAlg T A) ↔ ∃ k : ℕ, 2 ≤ k ∧ HasCyclicTermOp L A k) ∧
    ((∃ k : ℕ, 2 ≤ k ∧ HasCyclicTermOp L A k) ↔
      ∀ p : ℕ, p.Prime → Nat.card A < p → HasCyclicTermOp L A p) := by
  have h42 : (∃ T : TaylorDatum L, IsTaylorAlg T A) →
      ∀ p : ℕ, p.Prime → Nat.card A < p → HasCyclicTermOp L A p := by
    rintro ⟨T, hT⟩ p hp hpA
    exact cyclic_term_prime T hT p hp hpA
  have hex : (∀ p : ℕ, p.Prime → Nat.card A < p → HasCyclicTermOp L A p) →
      ∃ k : ℕ, 2 ≤ k ∧ HasCyclicTermOp L A k := by
    intro h
    obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (Nat.card A + 1)
    exact ⟨p, hp2.two_le, h p hp2 (by omega)⟩
  have htay : (∃ k : ℕ, 2 ≤ k ∧ HasCyclicTermOp L A k) → ∃ T : TaylorDatum L, IsTaylorAlg T A := by
    rintro ⟨k, hk, h⟩
    exact taylor_of_cyclic hid hk h
  exact ⟨⟨fun h => hex (h42 h), htay⟩, ⟨fun h => h42 (htay h), hex⟩⟩

end T41

end BKAbsorption

open BKAbsorption

theorem solution {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic] {A : Type w₁}
    [L.Structure A] [Finite A] (hid : IsIdempotent L A) :
    ((∃ T : TaylorDatum L, IsTaylorAlg T A) ↔ ∃ k : ℕ, 2 ≤ k ∧ HasCyclicTermOp L A k) ∧
    ((∃ k : ℕ, 2 ≤ k ∧ HasCyclicTermOp L A k) ↔
      ∀ p : ℕ, p.Prime → Nat.card A < p → HasCyclicTermOp L A p) :=
  T41.main hid
