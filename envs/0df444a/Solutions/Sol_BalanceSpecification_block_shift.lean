-- Prove2me | solution 1 for BalanceSpecification.block_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:32:13.874125+00:00
-- url     : https://prove2.me/submissions/6fd40d8b-3fcd-4c2c-aa09-269a715cb220

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block



set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
namespace BalanceSpecification
theorem _root_.solution (x : Configuration A) (k l : ℤ) (n : ℕ) :
    block (SymbolicDynamics.FullShift.shift k x) l n = block x (k + l) n := by
  simp only [block, SymbolicDynamics.FullShift.shift_apply, add_assoc]
end BalanceSpecification
