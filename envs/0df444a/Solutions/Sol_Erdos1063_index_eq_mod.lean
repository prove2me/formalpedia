-- Prove2me | solution 1 for Erdos1063.index_eq_mod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:59:59.302012+00:00
-- url     : https://prove2.me/submissions/ccaa2ac5-8e0f-4c97-b6b7-db84db992ae1

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
public import Theorems.Thm_Erdos1063_k_dvd

set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063
namespace Erdos1063
theorem _root_.solution {n k i0 : ℕ} (hkn : 2 * k ≤ n) (hk : 2 ≤ k) (hi0 : i0 < k)
    (hgood : ∀ i < k, i ≠ i0 → (n - i) ∣ n.choose k) : i0 = n % k := by
  obtain ⟨t, ht⟩ := k_dvd hkn hk hi0 hgood
  have h' : n = k * t + i0 := by omega
  rw [h', Nat.mul_add_mod, Nat.mod_eq_of_lt hi0]
end Erdos1063
