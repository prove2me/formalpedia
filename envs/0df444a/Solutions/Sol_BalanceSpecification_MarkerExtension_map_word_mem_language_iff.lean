-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.map_word_mem_language_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:28:37.152278+00:00
-- url     : https://prove2.me/submissions/ae1a2d5c-0c22-426a-ad69-028878917deb

module
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Theorems.Thm_BalanceSpecification_MarkerExtension_none_not_mem_map_some
public import Theorems.Thm_BalanceSpecification_MarkerExtension_marked_generated_infix
public import Theorems.Thm_BalanceSpecification_MarkerExtension_sourcePayload_mem_language
public import Theorems.Thm_BalanceSpecification_MarkerExtension_map_word_mem_language
public import Theorems.Thm_BalanceSpecification_language_codedShift_infix_generatedWords
public import Theorems.Thm_BalanceSpecification_language_factorial


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
omit [DiscreteTopology A] [Fintype A]
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution {v : Word A} :
    v.map some ∈ language (shift M hM x s) ↔ v ∈ language Y := by
  constructor
  · intro hv
    obtain ⟨z, hz, hsub⟩ := language_codedShift_infix_generatedWords hv
    have hP : (Set.range (sourcePayload M hM x s)).Nonempty := by
      obtain ⟨u⟩ := positiveLanguage_nonempty x
      exact ⟨_, u, rfl⟩
    obtain ⟨p, ⟨u, rfl⟩, hinfix⟩ := marked_generated_infix hP hz (none_not_mem_map_some v) hsub
    obtain ⟨q, hq, heq⟩ := List.infix_map_iff.mp hinfix
    have hvq : v = q := (List.map_inj_right (fun _ _ h => Option.some.inj h)).mp heq
    exact language_factorial Y (hvq ▸ hq) (sourcePayload_mem_language M hM x s u)
  · exact map_word_mem_language M hM x s
end BalanceSpecification.MarkerExtension
