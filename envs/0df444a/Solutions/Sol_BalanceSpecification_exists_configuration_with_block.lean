-- Prove2me | solution 1 for BalanceSpecification.exists_configuration_with_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:39:11.069711+00:00
-- url     : https://prove2.me/submissions/003087f4-592e-4074-8d73-929815536782

module
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Counting
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_GrowthTiling
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FactorialEntropy
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open scoped ENNReal
open BalanceSpecification
variable {A : Type*}
namespace BalanceSpecification
theorem _root_.solution [Nonempty A] (w : Word A) (k : ℤ) :
    ∃ x : Configuration A, block x k w.length = w := by
  classical
  let f : Fin w.length → ℤ := fun i => k + i.val
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    dsimp only [f] at hij
    omega
  let x : Configuration A := Function.extend f (fun i => w[i.val]) (fun _ => Classical.arbitrary A)
  refine ⟨x, ?_⟩
  apply List.ext_getElem
  · exact length_block _ _ _
  · intro i _ hi
    simpa only [block, List.getElem_ofFn, x, f] using
      hf.extend_apply (fun i => w[i.val]) (fun _ => Classical.arbitrary A) ⟨i, hi⟩
end BalanceSpecification
