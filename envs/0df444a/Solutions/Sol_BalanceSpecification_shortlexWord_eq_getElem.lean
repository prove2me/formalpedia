-- Prove2me | solution 1 for BalanceSpecification.shortlexWord_eq_getElem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:43:26.588646+00:00
-- url     : https://prove2.me/submissions/505770f1-19a6-4f1b-9db0-45a3b206f238

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Data.List.Shortlex
public import Mathlib.Data.List.Lex
public import Mathlib.Data.Finset.Sort
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Shortlex
public import Theorems.Thm_BalanceSpecification_shortlexThrough_prefix

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] [LinearOrder A]
variable [Nonempty A]
namespace BalanceSpecification
theorem _root_.solution {j n : ℕ} (hj : j < (shortlexThrough (A := A) n).length) :
    shortlexWord (A := A) j = (shortlexThrough n)[j] := by
  by_cases hjn : j ≤ n
  · exact (shortlexThrough_prefix hjn).getElem _
  · exact ((shortlexThrough_prefix (by omega : n ≤ j)).getElem hj).symm
end BalanceSpecification
