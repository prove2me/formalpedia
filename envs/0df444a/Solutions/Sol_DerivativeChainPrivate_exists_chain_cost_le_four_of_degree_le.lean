-- Prove2me | solution 1 for DerivativeChainPrivate.exists_chain_cost_le_four_of_degree_le
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-17T18:51:44.283363+00:00
-- url     : https://prove2.me/submissions/e9ba7c03-508a-4e06-81b4-16a0eed19529

import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_exists_chain_cost_le_sqrt
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
theorem solution {n : ℕ} (hn : 0 < n) (hn17 : n ≤ 17)
    (a : Fin n → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1) :
    ∃ z : Fin n → ℂ, IsChain a z ∧ chainCost z ≤ 4 := by
  obtain ⟨z, hz, hcost⟩ := exists_chain_cost_le_sqrt hn a ha
  refine ⟨z, hz, hcost.trans ?_⟩
  have hn16 : ((n - 1 : ℕ) : ℝ) ≤ 16 := by exact_mod_cast (show n - 1 ≤ 16 by omega)
  exact Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [hn16]⟩
