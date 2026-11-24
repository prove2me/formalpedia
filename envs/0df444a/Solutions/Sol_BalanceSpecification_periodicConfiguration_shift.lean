-- Prove2me | solution 1 for BalanceSpecification.periodicConfiguration_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:35:09.753185+00:00
-- url     : https://prove2.me/submissions/d7c0cb72-6eac-495b-a6a5-d11b340584d5

module
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Topology.Continuous
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Coded
public import Theorems.Thm_BalanceSpecification_nil_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block


attribute [local simp] BalanceSpecification.nil_mem_generatedWords

set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
namespace BalanceSpecification
theorem _root_.solution (w : Word A) (hw : 0 < w.length) :
    SymbolicDynamics.FullShift.shift (w.length : ℤ) (periodicConfiguration w hw) =
      periodicConfiguration w hw := by
  funext i
  simp only [SymbolicDynamics.FullShift.shift_apply, periodicConfiguration, Int.add_emod_left]
end BalanceSpecification
