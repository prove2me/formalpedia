-- Prove2me | solution 1 for Egrs75.MoveDigits.add_low_digit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:34.913075+00:00
-- url     : https://prove2.me/submissions/77431257-2ed7-4fa2-8e00-076a7a8f9f5f

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Definitions.Def_LeanPool_Egrs75_MoveDigits
public import Theorems.Thm_Egrs75_MoveDigits_add_carry_decomp
public import Theorems.Thm_Egrs75_RepairPaperfaithful_digitAt_add_low


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
theorem _root_.solution {q : ℕ} (hq : 1 < q) (n U i t : ℕ) (ht : t < i)
    (hlo : q ^ i ≤ n % q ^ i + U) :
    (n + U) / q ^ t % q = (n % q ^ i + U - q ^ i) / q ^ t % q := by
  have hdecomp := add_carry_decomp (by omega) n U i hlo
  have hlow := digitAt_add_low (p := q) (by omega) (k := i)
    (u := n % q ^ i + U - q ^ i) (h := n / q ^ i + 1) (i := t) ht
  unfold digitAt at hlow
  rwa [hdecomp]
end Egrs75.MoveDigits
