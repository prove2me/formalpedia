-- Prove2me | solution 1 for DerivativeChainPrivate.exists_chain_energy_of_step
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-17T18:47:22.683625+00:00
-- url     : https://prove2.me/submissions/5c05e98b-8426-4648-a2c5-e453dc1a1e76

import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_row_natDegree
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
open scoped BigOperators Polynomial
set_option autoImplicit false

/-!
# Exact derivative-row definitions and structural adapters

The four definitions below reproduce the definitions in the private mission
statement. No statement draft is imported. Rows are the actual, unnormalized
iterated derivatives: only the original row is asserted to be monic.
-/

open scoped BigOperators

namespace DerivativeChainPrivate











/-- Adjacent rows are related by the actual polynomial derivative. -/
theorem derivative_row_succ {n m : ℕ} (a : Fin n → ℂ) (hm : m < n) :
    Polynomial.derivative (row a (m + 1)) = row a m := by
  unfold row
  have h : n - m = (n - (m + 1)) + 1 := by omega
  rw [h, Function.iterate_succ_apply']









/-- Positive-numbered rows in range are nonconstant. -/
theorem row_degree_pos {n m : ℕ} (a : Fin n → ℂ) (hm0 : 0 < m) (hmn : m ≤ n) :
    0 < (row a m).degree := by
  rw [← Polynomial.natDegree_pos_iff_degree_pos, row_natDegree a hmn]
  exact hm0









end DerivativeChainPrivate

namespace DerivativeChainPrivate
end DerivativeChainPrivate
open DerivativeChainPrivate in
theorem solution
    (hstep : ∀ (P : Polynomial ℂ), 0 < P.degree → ∀ w : ℂ,
      P.derivative.eval w = 0 → ∃ v : ℂ,
        P.eval v = 0 ∧ ‖v - w‖ ^ 2 ≤ ‖v‖ ^ 2 - ‖w‖ ^ 2)
    {n : ℕ} (hn : 0 < n) (a : Fin n → ℂ) (u : ℂ)
    (hu : (row a 1).eval u = 0) :
    ∃ z : Fin n → ℂ, IsChain a z ∧ z ⟨0, hn⟩ = u ∧
      (∑ i : Fin (n - 1),
        ‖z ⟨i.val + 1, by omega⟩ - z ⟨i.val, by omega⟩‖ ^ 2) ≤
        ‖z ⟨n - 1, by omega⟩‖ ^ 2 - ‖u‖ ^ 2 := by
  classical
  let next (k : ℕ) (w : ℂ) : ℂ := Classical.epsilon (fun v : ℂ =>
    (row a (k + 2)).eval v = 0 ∧ ‖v - w‖ ^ 2 ≤ ‖v‖ ^ 2 - ‖w‖ ^ 2)
  have hnext (k : ℕ) (hk : k + 1 < n) (w : ℂ)
      (hw : (row a (k + 1)).eval w = 0) :
      (row a (k + 2)).eval (next k w) = 0 ∧
        ‖next k w - w‖ ^ 2 ≤ ‖next k w‖ ^ 2 - ‖w‖ ^ 2 := by
    dsimp only [next]
    apply Classical.epsilon_spec (p := fun v : ℂ =>
      (row a (k + 2)).eval v = 0 ∧ ‖v - w‖ ^ 2 ≤ ‖v‖ ^ 2 - ‖w‖ ^ 2)
    apply hstep (row a (k + 2)) (row_degree_pos a (by omega) (by omega)) w
    rw [show k + 2 = (k + 1) + 1 by omega, derivative_row_succ a hk]
    exact hw
  let x : ℕ → ℂ := Nat.rec u (fun k w => next k w)
  have hx0 : x 0 = u := rfl
  have hxs (k : ℕ) : x (k + 1) = next k (x k) := rfl
  have hxroot (k : ℕ) (hk : k < n) : (row a (k + 1)).eval (x k) = 0 := by
    induction k with
    | zero => simpa only [hx0] using hu
    | succ k ih =>
      rw [hxs]
      exact (hnext k hk (x k) (ih (by omega))).1
  have hxenergy (k : ℕ) (hk : k + 1 < n) :
      ‖x (k + 1) - x k‖ ^ 2 ≤ ‖x (k + 1)‖ ^ 2 - ‖x k‖ ^ 2 := by
    rw [hxs]
    exact (hnext k hk (x k) (hxroot k (by omega))).2
  let z : Fin n → ℂ := fun i => x i.val
  refine ⟨z, ?_, hx0, ?_⟩
  · intro i
    exact hxroot i.val i.isLt
  · change (∑ i : Fin (n - 1), ‖x (i.val + 1) - x i.val‖ ^ 2) ≤
      ‖x (n - 1)‖ ^ 2 - ‖u‖ ^ 2
    rw [Fin.sum_univ_eq_sum_range (fun k => ‖x (k + 1) - x k‖ ^ 2)]
    calc
      _ ≤ ∑ k ∈ Finset.range (n - 1), (‖x (k + 1)‖ ^ 2 - ‖x k‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro k hk
        exact hxenergy k (by have := Finset.mem_range.mp hk; omega)
      _ = ‖x (n - 1)‖ ^ 2 - ‖u‖ ^ 2 := by
        rw [Finset.sum_range_sub (fun k => ‖x k‖ ^ 2), hx0]
