-- Prove2me | solution 1 for BalanceSpecification.sGapListConcat_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:39:51.493904+00:00
-- url     : https://prove2.me/submissions/9e74c16c-46de-467b-812a-2d7be910a6f8

module
public import Definitions.Def_BalanceSpecificaton_SGap
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapRenewal

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution (s : ℕ) (ss : List ℕ) :
    sGapListConcat (s :: ss) = (true :: List.replicate s false) ++ sGapListConcat ss := rfl
end BalanceSpecification
