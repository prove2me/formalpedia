-- Prove2me | solution 2 for BalanceSpecification.block_prefix_tiles_suffix_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:38:12.312139+00:00
-- url     : https://prove2.me/submissions/55bc404e-38fe-410e-9ee4-4e927fbd6126

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_BlockingEstimate
public import Theorems.Thm_BalanceSpecification_block_chain_le

set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {H : ℕ → ℕ → ℝ}
namespace BalanceSpecification
theorem _root_.solution (hzero : ∀ s, H s 0 = 0)
    (hsub : ∀ s a b, H s (a + b) ≤ H s a + H (s + a) b)
    {r n k N : ℕ} (hfit : r + k * n ≤ N) :
    H 0 N ≤ H 0 r + (∑ j ∈ Finset.range k, H (r + j * n) n) +
      H (r + k * n) (N - (r + k * n)) := by
  have hlen : N = r + (k * n + (N - (r + k * n))) := by omega
  have hfirst := hsub 0 r (k * n + (N - (r + k * n)))
  rw [← hlen, zero_add] at hfirst
  have hsecond := hsub r (k * n) (N - (r + k * n))
  have htiles := block_chain_le hzero hsub r n k
  linarith only [hfirst, hsecond, htiles]
end BalanceSpecification
