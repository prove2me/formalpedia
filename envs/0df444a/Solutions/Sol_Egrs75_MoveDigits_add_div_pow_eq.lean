-- Prove2me | solution 1 for Egrs75.MoveDigits.add_div_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:29:52.533271+00:00
-- url     : https://prove2.me/submissions/b48b232a-36e2-495f-a18e-ccf4fb2a399f

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Definitions.Def_LeanPool_Egrs75_MoveDigits
public import Theorems.Thm_Egrs75_MoveDigits_add_carry_decomp

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
    (hlo : q ^ i ≤ n % q ^ i + U) (hhi : n % q ^ i + U < 2 * q ^ i) :
    (n + U) / q ^ i = n / q ^ i + 1 := by
  have hqi : 0 < q ^ i := pow_pos (by omega) i
  have hdecomp := add_carry_decomp (by omega) n U i hlo
  have hRlt : n % q ^ i + U - q ^ i < q ^ i := by omega
  rw [hdecomp, Nat.add_mul_div_left _ _ hqi, Nat.div_eq_of_lt hRlt, Nat.zero_add]
end Egrs75.MoveDigits
