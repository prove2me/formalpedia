-- Prove2me | solution 1 for BalanceSpecification.mem_renewalFinset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:39:55.35417+00:00
-- url     : https://prove2.me/submissions/4d778450-c874-494b-909b-2c7cb5691df6

module
public import Definitions.Def_BalanceSpecificaton_SGap
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapRenewal
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
attribute [local simp] BalanceSpecification.mem_wordFinset



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution {S : Set ℕ} {n : ℕ} {w : Word Bool} :
    w ∈ renewalFinset S n ↔ w ∈ generatedWords (sGapCode S) ∧ w.length = n :=
  mem_wordFinset
end BalanceSpecification
