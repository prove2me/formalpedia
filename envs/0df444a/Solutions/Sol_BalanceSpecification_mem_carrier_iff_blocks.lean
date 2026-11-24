-- Prove2me | solution 1 for BalanceSpecification.mem_carrier_iff_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:17:41.544671+00:00
-- url     : https://prove2.me/submissions/402ad5ce-5083-4330-9295-cce42e2fa435

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Theorems.Thm_BalanceSpecification_block_mem_language
public import Theorems.Thm_BalanceSpecification_exists_agreeOn_finset_of_blocks

set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution {x : Configuration A} :
    x ∈ X.carrier ↔ ∀ k n, block x k n ∈ language X := by
  constructor
  · intro hx k n
    exact block_mem_language hx k n
  · intro h
    apply X.isClosed.closure_subset
    apply mem_closure_iff.mpr
    intro U hU hxU
    obtain ⟨s, V, hV, hsub⟩ := isOpen_pi_iff.mp hU x hxU
    obtain ⟨y, hy, hxy⟩ := exists_agreeOn_finset_of_blocks h s
    refine ⟨y, hsub ?_, hy⟩
    intro i hi
    rw [hxy i hi]
    exact (hV i hi).2
end BalanceSpecification
