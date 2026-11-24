-- Prove2me | solution 1 for BalanceSpecification.codedShift_nonempty_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:57:38.728734+00:00
-- url     : https://prove2.me/submissions/6f958110-8092-43e3-a15b-9c223c1658f6

module
public import Definitions.Def_BalanceSpecificaton_Coded
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Theorems.Thm_BalanceSpecification_exists_nonempty_generator_of_codedShift_nonempty
public import Theorems.Thm_BalanceSpecification_codedShift_nonempty


set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
namespace BalanceSpecification
theorem _root_.solution [TopologicalSpace A] {C : Set (Word A)} :
    (codedShift C).carrier.Nonempty ↔ ∃ q ∈ C, 0 < q.length := by
  refine ⟨exists_nonempty_generator_of_codedShift_nonempty, ?_⟩
  rintro ⟨q, hqC, hq⟩
  exact codedShift_nonempty hqC hq
end BalanceSpecification
