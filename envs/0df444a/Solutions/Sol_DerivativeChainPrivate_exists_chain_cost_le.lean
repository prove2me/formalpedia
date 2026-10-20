-- Prove2me | solution 1 for DerivativeChainPrivate.exists_chain_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-17T18:50:17.933985+00:00
-- url     : https://prove2.me/submissions/73dfb10b-15bd-482e-9a14-c084dff8c85b

import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_exists_chain_cost_sq_le
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

namespace DerivativeChainPrivate
end DerivativeChainPrivate
open DerivativeChainPrivate in
theorem solution {n : ℕ} (hn : 0 < n) (a : Fin n → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ 1) (u : ℂ) (hu : (row a 1).eval u = 0) :
    ∃ z : Fin n → ℂ, IsChain a z ∧ z ⟨0, hn⟩ = u ∧
      chainCost z ≤ Real.sqrt (((n - 1 : ℕ) : ℝ) * (1 - ‖u‖ ^ 2)) := by
  obtain ⟨z, hz, hzu, hcost⟩ := exists_chain_cost_sq_le hn a ha u hu
  exact ⟨z, hz, hzu, Real.le_sqrt_of_sq_le hcost⟩
