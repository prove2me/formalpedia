-- Prove2me | solution 1 for BalanceSpecification.length_shortlexWord_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:48:20.016282+00:00
-- url     : https://prove2.me/submissions/d80b7e6c-b255-4be2-8af0-989172da64c5

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Data.List.Shortlex
public import Mathlib.Data.List.Lex
public import Mathlib.Data.Finset.Sort
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Shortlex

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] [LinearOrder A]
variable [Nonempty A]
namespace BalanceSpecification
theorem _root_.solution (j : ℕ) : (shortlexWord (A := A) j).length ≤ j := by
  exact mem_shortlexThrough.mp (List.getElem_mem _)
end BalanceSpecification
