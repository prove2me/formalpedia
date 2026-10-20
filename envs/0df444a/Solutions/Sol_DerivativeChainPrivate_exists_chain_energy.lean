-- Prove2me | solution 1 for DerivativeChainPrivate.exists_chain_energy
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-17T18:48:53.53398+00:00
-- url     : https://prove2.me/submissions/1c96c605-1b3c-414c-91ba-3c5473010956

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

namespace DerivativeChainPrivate
end DerivativeChainPrivate
open DerivativeChainPrivate in
theorem solution {n : ℕ} (hn : 0 < n) (a : Fin n → ℂ) (u : ℂ)
    (hu : (row a 1).eval u = 0) :
    ∃ z : Fin n → ℂ, IsChain a z ∧ z ⟨0, hn⟩ = u ∧
      (∑ i : Fin (n - 1),
        ‖z ⟨i.val + 1, by omega⟩ - z ⟨i.val, by omega⟩‖ ^ 2) ≤
        ‖z ⟨n - 1, by omega⟩‖ ^ 2 - ‖u‖ ^ 2 := by
  exact exists_chain_energy_of_step exists_root_energy hn a u hu
