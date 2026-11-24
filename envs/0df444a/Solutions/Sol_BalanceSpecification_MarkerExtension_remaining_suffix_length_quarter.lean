-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.remaining_suffix_length_quarter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:24:28.74266+00:00
-- url     : https://prove2.me/submissions/fd3a6c84-a8a8-4866-b486-903142b8df1a

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
theorem _root_.solution (M : ℕ) (s : ℕ → ℕ)
    (hsize : ∀ n : ℕ, 1 ≤ n → 4 * (n + M) ≤ s n)
    {l m : ℕ} (hm : 1 ≤ m) (hml : l ≤ s m) :
    4 * (l - min l (suffixLength M s m)) ≤ l := by
  have H := hsize m hm
  unfold suffixLength
  omega
end BalanceSpecification.MarkerExtension
