-- Prove2me | solution 1 for BalanceSpecification.shortlexWord_ne_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:57:55.448487+00:00
-- url     : https://prove2.me/submissions/4c59e59e-5573-4af7-a4a7-45eb029a519c

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Data.List.Shortlex
public import Mathlib.Data.List.Lex
public import Mathlib.Data.Finset.Sort
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Shortlex
public import Theorems.Thm_BalanceSpecification_shortlexWord_strictMono

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] [LinearOrder A]
variable [Nonempty A]
namespace BalanceSpecification
theorem _root_.solution {j : ℕ} (hj : 0 < j) : shortlexWord (A := A) j ≠ [] := by
  intro heq
  have h := shortlexWord_strictMono (A := A) hj
  rw [heq] at h
  exact List.not_shortlex_nil_right h
end BalanceSpecification
