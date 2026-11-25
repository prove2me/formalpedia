-- Prove2me | solution 1 for Erdos1063.carry_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:31:13.37316+00:00
-- url     : https://prove2.me/submissions/376b0c42-472f-479f-b2f3-58b7f5661dc2

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower

set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063
namespace Erdos1063
theorem _root_.solution {n k q : ℕ} (hq : 0 < q) (hkn : k ≤ n) :
    q ≤ k % q + (n - k) % q ↔ n % q < k % q := by
  have h1 : n % q = (k % q + (n - k) % q) % q := by
    rw [← Nat.add_mod]; congr 1; omega
  have hk := Nat.mod_lt k hq
  have hm := Nat.mod_lt (n - k) hq
  constructor
  · intro h
    rw [h1, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    omega
  · intro h
    by_contra h'
    push Not at h'
    rw [h1, Nat.mod_eq_of_lt h'] at h
    omega
end Erdos1063
