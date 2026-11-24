-- Prove2me | solution 1 for BalanceSpecification.getElem_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:31:04.388571+00:00
-- url     : https://prove2.me/submissions/a9f97fe2-6b79-43c1-b5de-e2de8624cdff

module
public import Mathlib.Dynamics.SymbolicDynamics.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Language
public import Theorems.Thm_BalanceSpecification_length_block
attribute [local simp] BalanceSpecification.length_block

set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution {A : Type*} (x : Configuration A) (k : ℤ)
    (n i : ℕ) (hi : i < n) : (block x k n)[i]'(by simpa [block] using hi) = x (k + i) := by
  simp only [block, List.getElem_ofFn]
end BalanceSpecification
