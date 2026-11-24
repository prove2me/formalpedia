-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.sourcePayload_length_of_large
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:24:11.661782+00:00
-- url     : https://prove2.me/submissions/5607bf44-1016-4b42-9596-ef18ed033d04

module
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Theorems.Thm_BalanceSpecification_MarkerExtension_sourcePayload_length

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
omit [DiscreteTopology A] [Fintype A] [TopologicalSpace (Option A)] [DiscreteTopology (Option A)]
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution
    (hs : ∀ n : ℕ, 1 ≤ n → n + M ≤ s n) (u : PositiveLanguage Y) :
    (sourcePayload M hM x s u).length = s u.val.length := by
  rw [sourcePayload_length]
  have H := hs u.val.length (by have := u.property.2; omega)
  unfold suffixLength
  omega
end BalanceSpecification.MarkerExtension
