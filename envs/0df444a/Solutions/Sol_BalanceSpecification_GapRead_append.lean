-- Prove2me | solution 1 for BalanceSpecification.GapRead.append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:43:07.782533+00:00
-- url     : https://prove2.me/submissions/918c1d6e-1b87-40ef-b6e8-b1f6673f2348

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGap

set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
open BalanceSpecification.GapRead
variable {S : Set ℕ} {a b c : ℕ} {u v : Word Bool}
namespace BalanceSpecification.GapRead
theorem _root_.solution (hu : GapRead S a u b) (hv : GapRead S b v c) :
    GapRead S a (u ++ v) c := by
  induction hu with
  | nil => exact hv
  | zero _ ih => exact .zero (ih hv)
  | one hs _ ih => exact .one hs (ih hv)
end BalanceSpecification.GapRead
