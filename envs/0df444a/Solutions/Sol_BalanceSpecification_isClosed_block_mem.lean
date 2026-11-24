-- Prove2me | solution 1 for BalanceSpecification.isClosed_block_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:39:44.751804+00:00
-- url     : https://prove2.me/submissions/17f022c0-6f0a-457d-8d8c-0f552cc8fb33

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
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_isClosed_wordCylinder
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
namespace BalanceSpecification
theorem _root_.solution (L : Set (Word A)) (k : ℤ) (n : ℕ) :
    IsClosed {x : Configuration A | block x k n ∈ L} := by
  have heq : {x : Configuration A | block x k n ∈ L} =
      ⋃ w ∈ wordFinset L n, wordCylinder w k := by
    ext x
    constructor
    · intro hx
      exact Set.mem_iUnion.mpr ⟨block x k n, Set.mem_iUnion.mpr
        ⟨mem_wordFinset.mpr ⟨hx, length_block _ _ _⟩, by change block x k (block x k n).length = block x k n; rw [length_block]⟩⟩
    · intro hx
      obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
      have hlen := (mem_wordFinset.mp hw).2
      have he : block x k n = w := by
        change block x k w.length = w at hxw
        simpa only [hlen] using hxw
      change block x k n ∈ L
      rw [he]
      exact (mem_wordFinset.mp hw).1
  rw [heq]
  exact isClosed_biUnion_finset fun w _ => isClosed_wordCylinder w k
end BalanceSpecification
