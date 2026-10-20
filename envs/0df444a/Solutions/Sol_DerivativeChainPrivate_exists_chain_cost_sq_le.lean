-- Prove2me | solution 1 for DerivativeChainPrivate.exists_chain_cost_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-17T18:48:52.311396+00:00
-- url     : https://prove2.me/submissions/48fb5efd-469b-40b0-a8d1-3755e7503d58

import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_exists_chain_energy_of_step
import Theorems.Thm_DerivativeChainPrivate_exists_root_energy
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









/-- The highest row is the original product polynomial. -/
@[simp] theorem row_top {n : ℕ} (a : Fin n → ℂ) : row a n = fromRoots a := by
  simp [row]



/-- The product polynomial is monic, including the empty product. -/
theorem fromRoots_monic {n : ℕ} (a : Fin n → ℂ) : (fromRoots a).Monic := by
  exact Polynomial.monic_prod_X_sub_C a Finset.univ

theorem fromRoots_ne_zero {n : ℕ} (a : Fin n → ℂ) : fromRoots a ≠ 0 :=
  (fromRoots_monic a).ne_zero









/-- The roots multiset retains every original root slot, with its multiplicity. -/
theorem fromRoots_roots {n : ℕ} (a : Fin n → ℂ) :
    (fromRoots a).roots = Finset.univ.val.map a := by
  unfold fromRoots
  rw [Polynomial.roots_prod _ _ (fromRoots_ne_zero a)]
  simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]

/-- Being a zero of the product is equivalent to being one of the given root slots. -/
theorem fromRoots_eval_eq_zero_iff {n : ℕ} (a : Fin n → ℂ) (z : ℂ) :
    (fromRoots a).eval z = 0 ↔ ∃ i : Fin n, z = a i := by
  change (fromRoots a).IsRoot z ↔ ∃ i : Fin n, z = a i
  rw [← Polynomial.mem_roots (fromRoots_ne_zero a), fromRoots_roots]
  simp [eq_comm]

/-- Every chain's last entry, when it exists, is one of the original roots. -/
theorem IsChain.last_mem_fromRoots {n : ℕ} {a z : Fin n → ℂ}
    (hz : IsChain a z) (hn : 0 < n) :
    ∃ i : Fin n, z ⟨n - 1, by omega⟩ = a i := by
  apply (fromRoots_eval_eq_zero_iff a _).mp
  have h := hz ⟨n - 1, by omega⟩
  simpa only [Nat.sub_add_cancel hn, row_top] using h

end DerivativeChainPrivate

/-!
# Deterministic compatible derivative chains from one-step energy selection

The explicit one-step hypothesis in this file is discharged by the polynomial
root-selection theorem in `Chain.lean`.
-/

open scoped BigOperators

namespace DerivativeChainPrivate



/-- Scalar Cauchy--Schwarz for the exact finite chain-cost definition. -/
theorem chainCost_sq_le_energy {n : ℕ} (z : Fin n → ℂ) :
    chainCost z ^ 2 ≤ ((n - 1 : ℕ) : ℝ) *
      ∑ i : Fin (n - 1),
        ‖z ⟨i.val + 1, by omega⟩ - z ⟨i.val, by omega⟩‖ ^ 2 := by
  simpa [chainCost] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin (n - 1) => (1 : ℝ))
    (fun i : Fin (n - 1) => ‖z ⟨i.val + 1, by omega⟩ - z ⟨i.val, by omega⟩‖)

/-- The unit-disk hypothesis is used only at the last vertex. -/
theorem exists_chain_cost_sq_le_of_step
    (hstep : ∀ (P : Polynomial ℂ), 0 < P.degree → ∀ w : ℂ,
      P.derivative.eval w = 0 → ∃ v : ℂ,
        P.eval v = 0 ∧ ‖v - w‖ ^ 2 ≤ ‖v‖ ^ 2 - ‖w‖ ^ 2)
    {n : ℕ} (hn : 0 < n) (a : Fin n → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ 1) (u : ℂ) (hu : (row a 1).eval u = 0) :
    ∃ z : Fin n → ℂ, IsChain a z ∧ z ⟨0, hn⟩ = u ∧
      chainCost z ^ 2 ≤ ((n - 1 : ℕ) : ℝ) * (1 - ‖u‖ ^ 2) := by
  obtain ⟨z, hz, hzu, he⟩ := exists_chain_energy_of_step hstep hn a u hu
  obtain ⟨j, hj⟩ := hz.last_mem_fromRoots hn
  have hlast : ‖z ⟨n - 1, by omega⟩‖ ^ 2 ≤ 1 := by
    rw [hj]
    nlinarith [ha j, norm_nonneg (a j)]
  refine ⟨z, hz, hzu, (chainCost_sq_le_energy z).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

end DerivativeChainPrivate

namespace DerivativeChainPrivate
end DerivativeChainPrivate
open DerivativeChainPrivate in
theorem solution {n : ℕ} (hn : 0 < n) (a : Fin n → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ 1) (u : ℂ) (hu : (row a 1).eval u = 0) :
    ∃ z : Fin n → ℂ, IsChain a z ∧ z ⟨0, hn⟩ = u ∧
      chainCost z ^ 2 ≤ ((n - 1 : ℕ) : ℝ) * (1 - ‖u‖ ^ 2) := by
  exact exists_chain_cost_sq_le_of_step exists_root_energy hn a ha u hu
