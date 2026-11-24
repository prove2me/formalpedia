-- Prove2me | solution 1 for BalanceSpecification.mem_interiors_of_mem_languageShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:39:51.431834+00:00
-- url     : https://prove2.me/submissions/2ba02321-b52a-4926-aae5-81cb13b93693

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
public import Theorems.Thm_BalanceSpecification_mem_languageShift_iff
public import Theorems.Thm_BalanceSpecification_block_append
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


attribute [local simp] BalanceSpecification.mem_languageShift_iff

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open scoped ENNReal
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A] [DiscreteTopology A]
variable [Fintype A]
omit [Fintype A]
namespace BalanceSpecification
theorem _root_.solution {L : Set (Word A)} {w : Word A}
    (hw : w ∈ language (languageShift L)) (M : ℕ) : w ∈ interiorLanguage L M := by
  obtain ⟨x, hx, k, hk⟩ := hw
  let p := block x (k - M) M
  let q := block x (k + w.length) M
  refine ⟨p, q, (length_block _ _ _).ge, (length_block _ _ _).ge, ?_⟩
  have hb := mem_languageShift_iff.mp hx (k - M) (M + w.length + M)
  have hstart : k - (M : ℤ) + ((M + w.length : ℕ) : ℤ) = k + w.length := by
    simp only [Nat.cast_add]
    omega
  rw [block_append, block_append, sub_add_cancel, hstart, hk] at hb
  exact hb
end BalanceSpecification
