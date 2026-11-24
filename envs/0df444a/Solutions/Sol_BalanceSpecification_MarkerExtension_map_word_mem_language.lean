-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.map_word_mem_language
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:27:39.315849+00:00
-- url     : https://prove2.me/submissions/4f111214-b055-417a-8460-cef6d4dfa601

module
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Theorems.Thm_BalanceSpecification_MarkerExtension_marker_followed_by_word
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
theorem _root_.solution {v : Word A} (hv : v ∈ language Y) :
    v.map some ∈ language (shift M hM x s) :=
  language_factorial (shift M hM x s) (List.suffix_append [none] (v.map some)).isInfix
    (marker_followed_by_word M hM x s hv)
end BalanceSpecification.MarkerExtension
