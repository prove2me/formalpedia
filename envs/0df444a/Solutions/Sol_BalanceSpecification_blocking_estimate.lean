-- Prove2me | solution 1 for BalanceSpecification.blocking_estimate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:39:47.742261+00:00
-- url     : https://prove2.me/submissions/f3752975-fdcd-44bb-8ba8-753da2d5b4f4

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_BlockingEstimate
public import Theorems.Thm_BalanceSpecification_blocking_estimate_two

set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {H : ℕ → ℕ → ℝ}
namespace BalanceSpecification
theorem _root_.solution {C : ℝ} (hC : 0 ≤ C)
    (hnonneg : ∀ s l, 0 ≤ H s l)
    (hsub : ∀ s a b, H s (a + b) ≤ H s a + H (s + a) b)
    (hbound : ∀ s l, H s l ≤ (l : ℝ) * C)
    {n N : ℕ} (hn : 0 < n) (hN : n ≤ N) :
    (n : ℝ) * H 0 N ≤ (∑ i ∈ Finset.range N, H i n) + 3 * (n : ℝ)^2 * C := by
  have h := blocking_estimate_two hC hnonneg hsub hbound hn hN
  have hterm : 0 ≤ (n : ℝ)^2 * C := mul_nonneg (sq_nonneg _) hC
  linarith only [h, hterm]
end BalanceSpecification
