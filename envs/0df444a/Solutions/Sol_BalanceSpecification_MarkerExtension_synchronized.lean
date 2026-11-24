-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.synchronized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:56:43.996309+00:00
-- url     : https://prove2.me/submissions/61ab8f55-9720-4208-9b5a-a088beb81d07

module
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Theorems.Thm_BalanceSpecification_MarkerExtension_marker_synchronizing
public import Theorems.Thm_BalanceSpecification_codedShift_irreducible


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
theorem _root_.solution : Synchronized (shift M hM x s) :=
  ⟨codedShift_irreducible _, [none], marker_synchronizing M hM x s⟩
end BalanceSpecification.MarkerExtension
