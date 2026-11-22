-- Prove2me | solution 1 for Egrs75.RepairPaperfaithful.lowDigits_add_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:36.896981+00:00
-- url     : https://prove2.me/submissions/f45b035f-34fb-4354-8348-82253753a55b

module
public import Definitions.Def_LeanPool_Egrs75_LeafInduction
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Theorems.Thm_Egrs75_RepairPaperfaithful_lowDigits_iff_digitAt
public import Theorems.Thm_Egrs75_RepairPaperfaithful_digitAt_add_low
public import Theorems.Thm_Egrs75_RepairPaperfaithful_digitAt_add_high

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.RepairPaperfaithful
open Nat
open Egrs75
open Egrs75.LeafInduction
namespace Egrs75.RepairPaperfaithful
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) {k u h : ℕ}
    (hu : u < p ^ k) (hlu : LowDigits p u) (hlh : LowDigits p h) :
    LowDigits p (u + p ^ k * h) := by
  rw [lowDigits_iff_digitAt hp] at hlu hlh ⊢
  intro i
  rcases lt_or_ge i k with hik | hki
  · rw [digitAt_add_low (by omega) hik]; exact hlu i
  · rw [digitAt_add_high hu hki]; exact hlh (i - k)
end Egrs75.RepairPaperfaithful
