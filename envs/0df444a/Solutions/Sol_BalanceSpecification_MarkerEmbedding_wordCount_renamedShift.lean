-- Prove2me | solution 1 for BalanceSpecification.MarkerEmbedding.wordCount_renamedShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:21:01.355181+00:00
-- url     : https://prove2.me/submissions/2dae0fc5-aed2-414f-a186-467da19973e1

module
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_Specification
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
public import Theorems.Thm_BalanceSpecification_MarkerEmbedding_wordFinset_renamedShift

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerEmbedding
variable {A B : Type*}
variable [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
  [TopologicalSpace B] [T2Space B]
namespace BalanceSpecification.MarkerEmbedding
theorem _root_.solution [Fintype B] {f : A → B} (hf : Function.Injective f)
    (Y : ShiftSpace A) (n : ℕ) :
    wordCount (language (renamedShift f Y)) n = wordCount (language Y) n := by
  classical
  unfold wordCount
  rw [wordFinset_renamedShift]
  apply Finset.card_image_of_injective
  intro u v h
  exact (List.map_inj_right (fun _ _ h => hf h)).mp h
end BalanceSpecification.MarkerEmbedding
