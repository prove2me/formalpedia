-- Prove2me | solution 1 for Egrs75.MoveDigits.add_digit_i
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:41.365371+00:00
-- url     : https://prove2.me/submissions/9d82a234-e396-4146-8295-c72009ab500b

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Definitions.Def_LeanPool_Egrs75_MoveDigits
public import Theorems.Thm_Egrs75_MoveDigits_add_div_pow_eq

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
theorem _root_.solution {q : ℕ} (hq : 1 < q) (n U i : ℕ)
    (hlo : q ^ i ≤ n % q ^ i + U) (hhi : n % q ^ i + U < 2 * q ^ i)
    (hbi : n / q ^ i % q < q - 1) :
    (n + U) / q ^ i % q = n / q ^ i % q + 1 := by
  rw [add_div_pow_eq hq n U i hlo hhi]
  have hd := Nat.div_add_mod (n / q ^ i) q
  have h1 : n / q ^ i + 1 = q * (n / q ^ i / q) + (n / q ^ i % q + 1) := by omega
  rw [h1, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
end Egrs75.MoveDigits
