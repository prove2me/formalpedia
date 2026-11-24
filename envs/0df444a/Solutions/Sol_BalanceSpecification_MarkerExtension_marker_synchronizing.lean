-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.marker_synchronizing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:25:38.392252+00:00
-- url     : https://prove2.me/submissions/69f536a8-e3ee-4922-a9ac-db3b3ae4218c

module
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Theorems.Thm_BalanceSpecification_MarkerExtension_marker_isSynchronizing

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*}
variable [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
  [TopologicalSpace (Option A)] [DiscreteTopology (Option A)]
omit [DiscreteTopology A] [Fintype A]
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution {Y : ShiftSpace A} (M : ℕ)
    (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
      ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
    (x : Y.carrier) (s : ℕ → ℕ) : IsSynchronizing (language (shift M hM x s)) [none] := by
  apply marker_isSynchronizing
  obtain ⟨u⟩ := positiveLanguage_nonempty x
  exact ⟨sourcePayload M hM x s u, u, rfl⟩
end BalanceSpecification.MarkerExtension
