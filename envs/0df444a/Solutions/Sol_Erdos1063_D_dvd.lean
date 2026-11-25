-- Prove2me | solution 1 for Erdos1063.D_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:48:44.765116+00:00
-- url     : https://prove2.me/submissions/585a7289-d5cb-420a-8bb4-06dca23f9617

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
public import Theorems.Thm_Erdos1063_prod_prime_pow_dvd
public import Theorems.Thm_Erdos1063_sharp_valuation_bound

set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063
namespace Erdos1063
theorem _root_.solution {n k e : ℕ} (hkn : 2 * k ≤ n) (hk : 2 ≤ k) (he : e < k)
    (hgood : ∀ i < k, i ≠ e → (n - i) ∣ n.choose k) :
    (∏ p ∈ k.primeFactors,
      p ^ (padicValNat p k + padicValNat p ((k - 1).choose e) + Nat.log p (max e (k - 1 - e))))
      ∣ n - e := by
  apply prod_prime_pow_dvd (fun p hp => (Nat.mem_primeFactors.mp hp).1)
  intro p hp
  rw [Nat.mem_primeFactors] at hp
  have := Fact.mk hp.1
  exact (padicValNat_dvd_iff_le (by omega)).mpr
    (sharp_valuation_bound hp.1 hkn hp.2.1 hk he hgood)
end Erdos1063
