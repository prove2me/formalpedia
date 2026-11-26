-- Prove2me | solution 1 for FixedOrderFactor.zetaN_empty_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:16.09679+00:00
-- url     : https://prove2.me/submissions/f383c33b-10d2-457e-ad54-bb7890b7ccc1

module
public import Definitions.Def_FixedOrderFactor_Order
public import Definitions.Def_FixedOrderFactor_Values
public import Theorems.Thm_FixedOrderFactor_zetaN_empty_eq

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {k : ℕ} (hk : k ≠ 0) :
    zetaN ∅ (2 * k) = (-1) ^ (k + 1) * 2 ^ (2 * k - 1) * π ^ (2 * k) *
      (bernoulli (2 * k) : ℝ) / (2 * k).factorial := by
  rw [zetaN_empty_eq (by omega), (hasSum_zeta_nat hk).tsum_eq]
end FixedOrderFactor
