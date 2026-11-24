-- Prove2me | solution 1 for BalanceSpecification.hasVariableSpecification_of_bounded_synchronizing_occurrences
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:22:17.719503+00:00
-- url     : https://prove2.me/submissions/e65cb542-4d98-4c81-a7cd-a3c211e039de

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Theorems.Thm_BalanceSpecification_exists_bounded_bridge_of_synchronizing_occurrences
public import Theorems.Thm_BalanceSpecification_language_factorial


set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*} {L : Set (Word A)}
namespace BalanceSpecification
theorem _root_.solution
    [TopologicalSpace A] {X : ShiftSpace A} {v : Word A}
    (hv : IsSynchronizing (language X) v) {N : ℕ}
    (hF : ∀ u ∈ language X, ∃ s : Word A,
      s.length ≤ N ∧ u ++ s ∈ language X ∧ v <:+: s)
    (hP : ∀ w ∈ language X, ∃ p : Word A,
      p.length ≤ N ∧ p ++ w ∈ language X ∧ v <:+: p) :
    HasVariableSpecification X := by
  refine ⟨2 * N, ?_⟩
  intro u hu w hw
  exact exists_bounded_bridge_of_synchronizing_occurrences
    (language_factorial X) hv (hF u hu) (hP w hw)
end BalanceSpecification
