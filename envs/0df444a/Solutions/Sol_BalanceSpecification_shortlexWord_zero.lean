-- Prove2me | solution 1 for BalanceSpecification.shortlexWord_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:49:21.74318+00:00
-- url     : https://prove2.me/submissions/12554fb3-64b5-49f8-ba99-2b3c7ccd4320

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Data.List.Shortlex
public import Mathlib.Data.List.Lex
public import Mathlib.Data.Finset.Sort
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Shortlex
public import Theorems.Thm_BalanceSpecification_length_shortlexWord_le

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] [LinearOrder A]
variable [Nonempty A]
namespace BalanceSpecification
theorem _root_.solution : shortlexWord (A := A) 0 = [] :=
  List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (length_shortlexWord_le 0))
end BalanceSpecification
