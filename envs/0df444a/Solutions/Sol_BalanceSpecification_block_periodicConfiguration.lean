-- Prove2me | solution 1 for BalanceSpecification.block_periodicConfiguration
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:45:41.184288+00:00
-- url     : https://prove2.me/submissions/14780037-c65c-4b5d-b63d-cd4c331294f2

module
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Topology.Continuous
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Coded
public import Theorems.Thm_BalanceSpecification_nil_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_periodicConfiguration_shift
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block


attribute [local simp] BalanceSpecification.nil_mem_generatedWords
attribute [local simp] BalanceSpecification.periodicConfiguration_shift

set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
namespace BalanceSpecification
theorem _root_.solution (w : Word A) (hw : 0 < w.length) (j : ℤ) :
    block (periodicConfiguration w hw) (j * w.length) w.length = w := by
  apply List.ext_getElem
  · exact length_block _ _ _
  · intro i hi hi'
    simp only [block, List.getElem_ofFn, periodicConfiguration]
    have hmod : (j * (w.length : ℤ) + (i : ℤ)) % w.length = i := by
      rw [Int.add_comm, Int.add_mul_emod_self_right,
        Int.emod_eq_of_lt (Nat.cast_nonneg i) (by exact_mod_cast hi')]
    simp only [hmod, Int.toNat_natCast]
end BalanceSpecification
