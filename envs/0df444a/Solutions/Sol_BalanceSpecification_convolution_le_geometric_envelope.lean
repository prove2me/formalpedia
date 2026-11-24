-- Prove2me | solution 1 for BalanceSpecification.convolution_le_geometric_envelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:25:46.607608+00:00
-- url     : https://prove2.me/submissions/66ddaf84-cbf6-4616-96fa-fb022ed6f9e1

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_RenewalBounds
public import Theorems.Thm_BalanceSpecification_convolution_le_pow_of_weighted_sum_bound
public import Theorems.Thm_BalanceSpecification_weighted_sum_le_of_geometric_bound

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution
    {a b : ℕ → ℝ} {θ ρ C : ℝ} (hθ : 0 ≤ θ) (hρ : 0 < ρ) (hθρ : θ < ρ)
    (hC : 0 ≤ C) (hb0 : ∀ l : ℕ, 0 ≤ b l)
    (hb : ∀ l : ℕ, b l ≤ C * θ ^ l) (ha : ∀ n : ℕ, a n ≤ ρ ^ n) (n : ℕ) :
    (∑ l ∈ Finset.range (n + 1), b l * a (n - l)) ≤
      (C / (1 - θ / ρ)) * ρ ^ n :=
  convolution_le_pow_of_weighted_sum_bound hρ hb0 ha
    (weighted_sum_le_of_geometric_bound hθ hρ hθρ hC hb) n
end BalanceSpecification
