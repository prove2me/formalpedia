-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.source_entropy_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:29:36.355923+00:00
-- url     : https://prove2.me/submissions/6908e7b2-7ccb-4a48-9436-ca71f59d865a

module
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Theorems.Thm_BalanceSpecification_MarkerExtension_renamed_source_subset
public import Theorems.Thm_BalanceSpecification_MarkerEmbedding_entropy_renamedShift
public import Theorems.Thm_BalanceSpecification_entropy_mono


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
theorem _root_.solution (hY : Y.carrier.Nonempty) :
    entropy Y hY ≤ entropy (shift M hM x s) (shift_nonempty M hM x s) := by
  have H := entropy_mono (MarkerEmbedding.renamedShift_nonempty (some : A → Option A) hY)
    (shift_nonempty M hM x s) (renamed_source_subset M hM x s)
  rw [MarkerEmbedding.entropy_renamedShift (f := (some : A → Option A)) (Option.some_injective A) hY] at H
  exact H
end BalanceSpecification.MarkerExtension
