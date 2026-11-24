-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.nonmarker_language
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:29:36.824069+00:00
-- url     : https://prove2.me/submissions/3b2a9b37-ab3c-43c1-a9c1-104cbdd803bd

module
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Theorems.Thm_BalanceSpecification_MarkerExtension_exists_map_some_of_markerFree
public import Theorems.Thm_BalanceSpecification_MarkerExtension_map_word_mem_language_iff

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
theorem _root_.solution {w : Word (Option A)}
    (hw : w ∈ language (shift M hM x s)) (hmarker : none ∉ w) :
    ∃ v ∈ language Y, w = v.map some := by
  obtain ⟨v, rfl⟩ := exists_map_some_of_markerFree hmarker
  exact ⟨v, (map_word_mem_language_iff M hM x s).mp hw, rfl⟩
end BalanceSpecification.MarkerExtension
