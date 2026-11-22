-- Prove2me | solution 1 for Egrs75.MoveDigits.add_high_frozen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:04.091693+00:00
-- url     : https://prove2.me/submissions/936791d5-a834-4982-9e9e-897a923e88b8

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Definitions.Def_LeanPool_Egrs75_MoveDigits
public import Theorems.Thm_Egrs75_MoveDigits_add_div_pow_eq
public import Theorems.Thm_Egrs75_MoveDigits_succ_div_pow_eq

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
theorem _root_.solution {q : ℕ} (hq : 1 < q) (n U i idx : ℕ)
    (hlo : q ^ i ≤ n % q ^ i + U) (hhi : n % q ^ i + U < 2 * q ^ i)
    (hbi : n / q ^ i % q < q - 1) (hidx : i < idx) :
    (n + U) / q ^ idx % q = n / q ^ idx % q := by
  have hsplit : q ^ idx = q ^ i * q ^ (idx - i) := by
    rw [← pow_add]; congr 1; omega
  have h1 : (n + U) / q ^ idx = (n + U) / q ^ i / q ^ (idx - i) := by
    rw [hsplit, Nat.div_div_eq_div_mul]
  have h2 : n / q ^ idx = n / q ^ i / q ^ (idx - i) := by
    rw [hsplit, Nat.div_div_eq_div_mul]
  rw [h1, h2, add_div_pow_eq hq n U i hlo hhi,
    succ_div_pow_eq hq hbi (by omega : 1 ≤ idx - i)]
end Egrs75.MoveDigits
