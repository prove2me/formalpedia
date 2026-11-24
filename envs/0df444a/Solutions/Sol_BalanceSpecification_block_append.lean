-- Prove2me | solution 1 for BalanceSpecification.block_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:32:03.303378+00:00
-- url     : https://prove2.me/submissions/750b3426-32ab-4825-8fd0-4899d0d3ffbc

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
theorem _root_.solution (x : Configuration A) (k : ℤ) (m n : ℕ) :
    block x k (m + n) = block x k m ++ block x (k + m) n := by
  simp only [block, List.ofFn_add, Fin.val_castLE, Fin.val_natAdd,
    Int.natCast_add, add_assoc]
end BalanceSpecification
