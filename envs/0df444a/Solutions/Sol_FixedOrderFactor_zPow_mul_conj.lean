-- Prove2me | solution 1 for FixedOrderFactor.zPow_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:03:06.609198+00:00
-- url     : https://prove2.me/submissions/27cf1560-cb37-4e4e-8310-53443afa4e13

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Pairs
public import Definitions.Def_FixedOrderFactor_ModelPairs
public import Theorems.Thm_FixedOrderFactor_omega_ne_zero
public import Theorems.Thm_FixedOrderFactor_conj_omega
public import Theorems.Thm_FixedOrderFactor_rootOfUnity_eq_omega

set_option autoImplicit true
@[expose] public section
public section
open Finset Complex
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (r : ℕ) (S : Finset Nat.Primes) (j : S → Fin r) (m n : ℕ) :
    zPow r S j m * starRingEnd ℂ (zPow r S j n) =
      ∏ q : S, ω r ^ (((j q : ℕ) : ℤ) *
        ((m.factorization (q : Nat.Primes) : ℤ) - n.factorization (q : Nat.Primes))) := by
  unfold zPow
  rw [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun q _ => ?_)
  rw [rootOfUnity_eq_omega, rootOfUnity_eq_omega, map_pow, conj_omega, inv_pow,
    ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ (omega_ne_zero r)]
  congr 1
  push_cast; ring
end FixedOrderFactor
