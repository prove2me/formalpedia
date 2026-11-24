-- Prove2me | solution 1 for BalanceSpecification.finite_carrier_iff_bounded_wordCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:17:52.967958+00:00
-- url     : https://prove2.me/submissions/1ea99fea-4374-4614-9e7d-fb605d6ab320

module
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Definitions.Def_BalanceSpecificaton_Specification
public import Mathlib.Data.Set.Card
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Theorems.Thm_BalanceSpecification_finite_carrier_of_bounded_wordCount
public import Theorems.Thm_BalanceSpecification_wordCount_le_ncard_of_finite_carrier

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*}
variable [Fintype A] [TopologicalSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution : X.carrier.Finite ↔
    ∃ C : ℕ, ∀ n, wordCount (language X) n ≤ C := by
  constructor
  · intro hX
    exact ⟨X.carrier.ncard, wordCount_le_ncard_of_finite_carrier hX⟩
  · exact finite_carrier_of_bounded_wordCount
end BalanceSpecification
