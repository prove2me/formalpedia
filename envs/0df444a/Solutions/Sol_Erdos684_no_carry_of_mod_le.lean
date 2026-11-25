-- Prove2me | solution 1 for Erdos684.no_carry_of_mod_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:40:17.829986+00:00
-- url     : https://prove2.me/submissions/d012bafc-089c-4f9a-bcad-19abaa68a7f7

module
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos684_Finite

set_option autoImplicit false
@[expose] public section
public section
open Erdos684
namespace Erdos684
theorem _root_.solution {n k q : ℕ} (hkn : k ≤ n) (hq : 0 < q)
    (hmod : k % q ≤ n % q) : k % q + (n - k) % q < q := by
  have ha := Nat.mod_lt k hq
  have hb := Nat.mod_lt (n - k) hq
  have hsum := Nat.add_mod k (n - k) q
  rw [Nat.add_sub_of_le hkn] at hsum
  by_contra h
  have hle : q ≤ k % q + (n - k) % q := by omega
  have hlt : k % q + (n - k) % q - q < q := by omega
  rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt hlt] at hsum
  omega
end Erdos684
