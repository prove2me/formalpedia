-- Prove2me | solution 1 for BalanceSpecification.sGapConcat_mem_generatedWords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:36:16.878004+00:00
-- url     : https://prove2.me/submissions/d4594b90-5369-4486-9dee-945102033a94

module
public import Definitions.Def_BalanceSpecificaton_SGap
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapRenewal
public import Theorems.Thm_BalanceSpecification_sGapListConcat_mem_generatedWords

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution {S : Set ℕ} {r : ℕ} {f : Fin r → ℕ}
    (hf : ∀ i, f i ∈ S) : sGapConcat f ∈ generatedWords (sGapCode S) := by
  apply sGapListConcat_mem_generatedWords
  intro s hs
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
  exact hf i
end BalanceSpecification
