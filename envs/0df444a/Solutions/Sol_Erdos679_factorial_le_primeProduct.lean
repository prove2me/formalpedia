-- Prove2me | solution 1 for Erdos679.factorial_le_primeProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:20:30.944268+00:00
-- url     : https://prove2.me/submissions/8928789f-e09e-46eb-9c64-a4f9aac7e8d4

module
public import Definitions.Def_Erdos679_StirlingBound
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos679_Analytic
public import Theorems.Thm_Erdos679_primeProduct_succ

set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos679
namespace Erdos679
theorem _root_.solution (m : ℕ) : m.factorial ≤ primeProduct m := by
  induction m with
  | zero => simp [primeProduct]
  | succ m ih =>
    rw [Nat.factorial_succ, primeProduct_succ]
    have hp := Nat.add_two_le_nth_prime m
    exact Nat.mul_le_mul (by omega : m + 1 ≤ Nat.nth Nat.Prime m)
      ih |>.trans_eq (Nat.mul_comm _ _)
end Erdos679
