-- Prove2me | solution 1 for Egrs75.MoveDigits.succ_div_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:34.362492+00:00
-- url     : https://prove2.me/submissions/4382dfee-92ec-45bf-b411-03aefe826899

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
theorem _root_.solution {q : ℕ} (hq : 1 < q) {H : ℕ} (hH : H % q < q - 1)
    {s : ℕ} (hs : 1 ≤ s) : (H + 1) / q ^ s = H / q ^ s := by
  have hq0 : 0 < q := by omega
  have hHq : (H + 1) / q = H / q := by
    have hd := Nat.div_add_mod H q
    have h1 : H + 1 = q * (H / q) + (H % q + 1) := by omega
    rw [h1, Nat.mul_add_div hq0,
      Nat.div_eq_of_lt (show H % q + 1 < q by omega), Nat.add_zero]
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  rw [pow_succ, mul_comm (q ^ t) q, ← Nat.div_div_eq_div_mul,
    ← Nat.div_div_eq_div_mul, hHq]
end Egrs75.MoveDigits
