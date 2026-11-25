-- Prove2me | solution 1 for Erdos1063.W_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:47:47.530106+00:00
-- url     : https://prove2.me/submissions/5a57005f-d467-4028-bb9f-b370b2432c75

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
public import Theorems.Thm_Erdos1063_valuation_bound
public import Theorems.Thm_Erdos1063_prod_prime_pow_dvd

set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063
namespace Erdos1063
theorem _root_.solution {n k i0 : ℕ} (hkn : 2 * k ≤ n) (hk : 2 ≤ k) (hi0 : i0 < k)
    (hgood : ∀ i < k, i ≠ i0 → (n - i) ∣ n.choose k) : W k ∣ n - i0 := by
  unfold W
  apply prod_prime_pow_dvd (fun p hp => (Nat.mem_primeFactors.mp hp).1)
  · intro p hp
    rw [Nat.mem_primeFactors] at hp
    have := Fact.mk hp.1
    have hpos : n - i0 ≠ 0 := by omega
    exact (padicValNat_dvd_iff_le hpos).mpr (valuation_bound hp.1 hkn hp.2.1 hk hgood)
end Erdos1063
