-- Prove2me | solution 1 for BalanceSpecification.sGapConcat_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:37:03.900855+00:00
-- url     : https://prove2.me/submissions/8521e818-8033-44cc-af97-bd7f2db7f468

module
public import Definitions.Def_BalanceSpecificaton_SGap
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapRenewal
public import Theorems.Thm_BalanceSpecification_sGapListConcat_injective

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution {r : ℕ} : Function.Injective (@sGapConcat r) := by
  intro f g h
  exact List.ofFn_injective (sGapListConcat_injective h)
end BalanceSpecification
