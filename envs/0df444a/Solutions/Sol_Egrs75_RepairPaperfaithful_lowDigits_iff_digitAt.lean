-- Prove2me | solution 1 for Egrs75.RepairPaperfaithful.lowDigits_iff_digitAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:27:16.757258+00:00
-- url     : https://prove2.me/submissions/b4012024-6698-42ed-9589-ae4818cbf861

module
public import Definitions.Def_LeanPool_Egrs75_LeafInduction
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.RepairPaperfaithful
open Nat
open Egrs75
open Egrs75.LeafInduction
namespace Egrs75.RepairPaperfaithful
theorem _root_.solution {p n : ℕ} (hp : 2 ≤ p) :
    LowDigits p n ↔ ∀ i, digitAt p i n ≤ (p - 1) / 2 := by
  unfold LowDigits digitAt
  constructor
  · intro h i
    rw [← getD_digits n i hp]
    -- getD i 0 is either a member (in range) or 0 (out of range)
    rcases lt_or_ge i (Nat.digits p n).length with hi | hi
    · simp_all
    · simp_all
  · intro h d hd
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hd
    rw [← List.getD_eq_getElem _ 0 hi, getD_digits n i hp]
    exact h i
end Egrs75.RepairPaperfaithful
