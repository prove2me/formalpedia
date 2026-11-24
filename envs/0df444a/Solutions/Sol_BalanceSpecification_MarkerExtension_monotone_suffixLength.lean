-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.monotone_suffixLength
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:23:42.420096+00:00
-- url     : https://prove2.me/submissions/a251f633-94d5-49e8-8ff3-ab8725387e46

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerSuffix

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*} [TopologicalSpace A] {Y : ShiftSpace A}
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution (M : ℕ) {s : ℕ → ℕ} (hs : StrictMono s) :
    Monotone (suffixLength M s) := by
  apply monotone_nat_of_le_succ
  intro n
  have H := hs (Nat.lt_succ_self n)
  change s n - n - M ≤ s (n + 1) - (n + 1) - M
  change s n < s (n + 1) at H
  omega
end BalanceSpecification.MarkerExtension
