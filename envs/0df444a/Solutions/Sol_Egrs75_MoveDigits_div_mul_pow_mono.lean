-- Prove2me | solution 1 for Egrs75.MoveDigits.div_mul_pow_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:28:48.380397+00:00
-- url     : https://prove2.me/submissions/b5aa31e7-a781-42fd-820e-aa62a803d24d

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Definitions.Def_LeanPool_Egrs75_MoveDigits

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.MoveDigits
open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful
namespace Egrs75.MoveDigits
theorem _root_.solution {q : ℕ} (_hq : 0 < q) (n : ℕ) {a b : ℕ} (hab : a ≤ b) :
    n / q ^ b * q ^ b ≤ n / q ^ a * q ^ a := by
  have hsplit : q ^ b = q ^ a * q ^ (b - a) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit, ← Nat.div_div_eq_div_mul]
  have h1 : n / q ^ a / q ^ (b - a) * q ^ (b - a) ≤ n / q ^ a :=
    Nat.div_mul_le_self _ _
  calc n / q ^ a / q ^ (b - a) * (q ^ a * q ^ (b - a))
      = n / q ^ a / q ^ (b - a) * q ^ (b - a) * q ^ a := by ring
    _ ≤ n / q ^ a * q ^ a := Nat.mul_le_mul_right _ h1
end Egrs75.MoveDigits
