-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.renamed_source_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:28:36.57049+00:00
-- url     : https://prove2.me/submissions/6878f5c8-602c-4ec8-ba60-fb7764ffcd47

module
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Theorems.Thm_BalanceSpecification_MarkerExtension_map_word_mem_language
public import Theorems.Thm_BalanceSpecification_MarkerEmbedding_mem_language_renamedShift_iff
public import Theorems.Thm_BalanceSpecification_carrier_subset_of_language_subset


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*}
variable [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
  [TopologicalSpace (Option A)] [DiscreteTopology (Option A)]
variable {Y : ShiftSpace A} (M : ℕ)
  (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
    ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
  (x : Y.carrier) (s : ℕ → ℕ)
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution :
    (MarkerEmbedding.renamedShift (some : A → Option A) Y).carrier ⊆ (shift M hM x s).carrier := by
  apply carrier_subset_of_language_subset
  intro w hw
  obtain ⟨v, hv, rfl⟩ := (MarkerEmbedding.mem_language_renamedShift_iff (some : A → Option A)).mp hw
  exact map_word_mem_language M hM x s hv
end BalanceSpecification.MarkerExtension
