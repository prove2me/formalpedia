-- Prove2me | solution 1 for Erdos684.dvd_add_residue_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:48:02.005649+00:00
-- url     : https://prove2.me/submissions/cea87d9f-2c22-4504-a6da-2237a2f14ec0

module
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos684_BadPrimes

set_option autoImplicit false
@[expose] public section
public section
open Erdos684
namespace Erdos684
theorem _root_.solution (n p : ℕ) (hp : 0 < p) :
    p ∣ n + (p - n % p) := by
  have hr := Nat.mod_lt n hp
  have hdecomp := Nat.mod_add_div n p
  refine ⟨n / p + 1, ?_⟩
  rw [Nat.mul_add, Nat.mul_one]
  omega
end Erdos684
