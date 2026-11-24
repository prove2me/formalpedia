-- Prove2me | solution 1 for BalanceSpecification.zero_entropy_balanced_specification_equivalences
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:55:45.095247+00:00
-- url     : https://prove2.me/submissions/32c5f5cb-f846-4c2b-be13-75ecafb2469e

module
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Definitions.Def_BalanceSpecificaton_Specification
public import Mathlib.Data.Set.Card
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Theorems.Thm_BalanceSpecification_bsm_iff_hasVariableSpecification_of_entropy_zero
public import Theorems.Thm_BalanceSpecification_biBalanced_of_hasVariableSpecification
public import Theorems.Thm_BalanceSpecification_boundedlySupermultiplicative_of_leftBalanced
public import Theorems.Thm_BalanceSpecification_boundedlySupermultiplicative_of_rightBalanced
public import Theorems.Thm_BalanceSpecification_language_factorial


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*}
variable [Fintype A] [TopologicalSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution (hX : X.carrier.Nonempty)
    (hh : entropy X hX = 0) (hirr : Irreducible X) :
    (HasVariableSpecification X ↔ BiBalanced (language X)) ∧
    (BiBalanced (language X) ↔ RightBalanced (language X) ∨ LeftBalanced (language X)) ∧
    ((RightBalanced (language X) ∨ LeftBalanced (language X)) ↔
      BoundedlySupermultiplicative (language X)) := by
  have hbsm_spec := bsm_iff_hasVariableSpecification_of_entropy_zero hX hh hirr
  have hone_bsm : (RightBalanced (language X) ∨ LeftBalanced (language X)) →
      BoundedlySupermultiplicative (language X) := by
    rintro (hr | hl)
    · exact boundedlySupermultiplicative_of_rightBalanced (language_factorial X) hr
    · exact boundedlySupermultiplicative_of_leftBalanced (language_factorial X) hl
  refine ⟨⟨biBalanced_of_hasVariableSpecification hX, ?_⟩, ⟨?_, ?_⟩, ⟨hone_bsm, ?_⟩⟩
  · intro hbi
    exact hbsm_spec.mp (hone_bsm (Or.inl hbi.1))
  · intro hbi
    exact Or.inl hbi.1
  · intro hone
    exact biBalanced_of_hasVariableSpecification hX (hbsm_spec.mp (hone_bsm hone))
  · intro hbsm
    exact Or.inl (biBalanced_of_hasVariableSpecification hX (hbsm_spec.mp hbsm)).1
end BalanceSpecification
