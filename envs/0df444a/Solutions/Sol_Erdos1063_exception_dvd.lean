-- Prove2me | solution 1 for Erdos1063.exception_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:05:30.063879+00:00
-- url     : https://prove2.me/submissions/5461ae56-c024-4a45-9a4d-34f3b01c5c84

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
public import Theorems.Thm_Erdos1063_index_eq_mod
public import Theorems.Thm_Erdos1063_D_dvd

set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063
namespace Erdos1063
theorem _root_.solution {n k e : ℕ} (hk : 2 ≤ k) (h : 2 * k ≤ n) (he : e < k)
    (hgood : ∀ i < k, i ≠ e → (n - i) ∣ n.choose k) :
    e = n % k ∧
      ∏ p ∈ k.primeFactors,
        p ^ (padicValNat p k + padicValNat p ((k - 1).choose e) + Nat.log p (max e (k - 1 - e)))
        ∣ n - e :=
  ⟨index_eq_mod h hk he hgood, D_dvd h hk he hgood⟩
end Erdos1063
