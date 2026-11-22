-- Prove2me | solution 1 for Egrs75.MoveDigits.add_carry_decomp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:28:48.780409+00:00
-- url     : https://prove2.me/submissions/16c34a4f-0c27-4680-bd82-5e2daf256c0a

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
theorem _root_.solution {q : ℕ} (hq : 1 ≤ q) (n U i : ℕ)
    (hlo : q ^ i ≤ n % q ^ i + U) :
    n + U = (n % q ^ i + U - q ^ i) + q ^ i * (n / q ^ i + 1) := by
  have hqi : 0 < q ^ i := pow_pos (by omega) i
  have hsplit : n = n % q ^ i + q ^ i * (n / q ^ i) := (Nat.mod_add_div n (q ^ i)).symm
  have hmul : q ^ i * (n / q ^ i + 1) = q ^ i * (n / q ^ i) + q ^ i := by ring
  omega
end Egrs75.MoveDigits
