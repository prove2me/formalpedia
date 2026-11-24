-- Prove2me | solution 1 for BalanceSpecification.exists_nonempty_generator_of_codedShift_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:56:16.233558+00:00
-- url     : https://prove2.me/submissions/bd79d167-4069-4115-b620-b2b269b2d193

module
public import Definitions.Def_BalanceSpecificaton_Coded
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Theorems.Thm_BalanceSpecification_length_block
attribute [local simp] BalanceSpecification.length_block



set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
namespace BalanceSpecification
theorem _root_.solution [TopologicalSpace A]
    {C : Set (Word A)} (hX : (codedShift C).carrier.Nonempty) :
    ∃ q ∈ C, 0 < q.length := by
  obtain ⟨x, hx⟩ := hX
  obtain ⟨y, _, hy⟩ := mem_closure_iff.mp hx Set.univ isOpen_univ (Set.mem_univ _)
  obtain ⟨p, hp, hwords⟩ := hy
  refine ⟨block y (p 0) ((p (0 + 1) - p 0).toNat), hwords 0, ?_⟩
  rw [length_block]
  have hp1 := hp (show (0 : ℤ) < 0 + 1 by omega)
  omega
end BalanceSpecification
