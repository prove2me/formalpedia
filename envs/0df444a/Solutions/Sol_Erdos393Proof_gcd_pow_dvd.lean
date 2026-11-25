-- Prove2me | solution 1 for Erdos393Proof.gcd_pow_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:23:04.367315+00:00
-- url     : https://prove2.me/submissions/ba454ef4-c76f-4ffb-876c-0baaf322f23a

module
public import Mathlib
public import Definitions.Def_Erdos393Palomar_Solution

set_option autoImplicit true
@[expose] public section
public section
open Filter Asymptotics
open scoped Nat
open Erdos393Proof
open ABC Polynomial
namespace Erdos393Proof
theorem _root_.solution (a b : ℕ) : ∀ j : ℕ, Nat.gcd b (a ^ j) ∣ Nat.gcd b a ^ j := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_succ]
    exact (Nat.gcd_mul_right_dvd_mul_gcd b (a ^ j) a).trans
      (Nat.mul_dvd_mul_right ih _)
end Erdos393Proof
