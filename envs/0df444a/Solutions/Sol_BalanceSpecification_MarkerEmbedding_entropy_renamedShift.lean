-- Prove2me | solution 1 for BalanceSpecification.MarkerEmbedding.entropy_renamedShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:21:51.235487+00:00
-- url     : https://prove2.me/submissions/28acb446-2a24-43d3-86cc-8e3beaa6f503

module
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_Specification
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
public import Theorems.Thm_BalanceSpecification_MarkerEmbedding_wordCount_renamedShift

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
    {Y : ShiftSpace A} (hY : Y.carrier.Nonempty) :
    entropy (renamedShift f Y) (renamedShift_nonempty f hY) = entropy Y hY := by
  unfold entropy
  congr 1
  funext n
  rw [wordCount_renamedShift hf]
end BalanceSpecification.MarkerEmbedding
