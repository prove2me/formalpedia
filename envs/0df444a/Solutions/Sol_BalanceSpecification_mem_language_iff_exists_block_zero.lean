-- Prove2me | solution 1 for BalanceSpecification.mem_language_iff_exists_block_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:33:21.476063+00:00
-- url     : https://prove2.me/submissions/afccc0b3-de6d-41c8-a9f7-77508e894b12

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Theorems.Thm_BalanceSpecification_block_shift
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block



set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution {w : Word A} :
    w ∈ language X ↔ ∃ x ∈ X.carrier, block x 0 w.length = w := by
  constructor
  · rintro ⟨x, hx, k, hk⟩
    refine ⟨SymbolicDynamics.FullShift.shift k x, X.mapsTo k hx, ?_⟩
    simpa only [block_shift, add_zero] using hk
  · rintro ⟨x, hx, hk⟩
    exact ⟨x, hx, 0, hk⟩
end BalanceSpecification
