-- Prove2me | solution 1 for BalanceSpecification.sGapListConcat_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:36:07.45526+00:00
-- url     : https://prove2.me/submissions/cf00439a-6f4d-4ba3-a242-683e68664380

module
public import Definitions.Def_BalanceSpecificaton_SGap
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapRenewal
public import Theorems.Thm_BalanceSpecification_first_sGap_generator_unique
public import Theorems.Thm_BalanceSpecification_sGapListConcat_nil_or_marker

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution : Function.Injective sGapListConcat := by
  intro ss
  induction ss with
  | nil =>
    intro ts h
    cases ts with
    | nil => rfl
    | cons t ts => cases h
  | cons s ss ih =>
    intro ts h
    cases ts with
    | nil => cases h
    | cons t ts =>
      obtain ⟨hst, htail⟩ := first_sGap_generator_unique
        (sGapListConcat_nil_or_marker ss) (sGapListConcat_nil_or_marker ts) h
      exact congrArg₂ List.cons hst (ih htail)
end BalanceSpecification
