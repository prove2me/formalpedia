-- Prove2me | solution 1 for FixedOrderFactor.zetaN_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:59:55.085577+00:00
-- url     : https://prove2.me/submissions/19baffb6-74be-4463-9bab-a6d058cec00d

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Euler
public import Theorems.Thm_FixedOrderFactor_pow_inv_q_lt_one
public import Theorems.Thm_FixedOrderFactor_zetaN_eq_mul_prod

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) {s : ℕ} (hs : 2 ≤ s) :
    zetaN N s = zetaN ∅ s * ∏ q ∈ N, (1 - (1 / (q : ℝ)) ^ s) := by
  have hprod : (∏ q ∈ N, (1 - (1 / (q : ℝ)) ^ s)⁻¹) * ∏ q ∈ N, (1 - (1 / (q : ℝ)) ^ s) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one (fun q _ => inv_mul_cancel₀ (sub_ne_zero.mpr
      (pow_inv_q_lt_one q (by omega)).ne'))
  rw [zetaN_eq_mul_prod N hs]
  linear_combination (-zetaN N s) * hprod
end FixedOrderFactor
