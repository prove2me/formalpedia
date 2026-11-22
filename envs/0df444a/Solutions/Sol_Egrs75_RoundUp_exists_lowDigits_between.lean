-- Prove2me | solution 1 for Egrs75.RoundUp.exists_lowDigits_between
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:36.093799+00:00
-- url     : https://prove2.me/submissions/2ce2aadf-44b4-4043-9478-51cfc52836c2

module
public import Definitions.Def_LeanPool_Egrs75_Defs
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Data.Finset.Attr
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Theorems.Thm_Egrs75_RoundUp_lowDigits_ru
public import Theorems.Thm_Egrs75_RoundUp_ru_bounds

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.RoundUp
open Nat
open Egrs75
variable (p : ℕ)
namespace Egrs75.RoundUp
theorem _root_.solution {p : ℕ} (hp : 3 ≤ p) (hodd : Odd p) (x : ℕ)
    (hx : 1 ≤ x) : ∃ m, x ≤ m ∧ m < 2 * x ∧ LowDigits p m := by
  obtain ⟨hlo, hhi⟩ := ru_bounds hp hodd x hx
  exact ⟨ru p x, hlo, hhi, lowDigits_ru hp x⟩
end Egrs75.RoundUp
