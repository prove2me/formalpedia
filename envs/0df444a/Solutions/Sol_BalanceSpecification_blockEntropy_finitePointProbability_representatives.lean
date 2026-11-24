-- Prove2me | solution 1 for BalanceSpecification.blockEntropy_finitePointProbability_representatives
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:18:30.787057+00:00
-- url     : https://prove2.me/submissions/dfd285ee-e97d-42b1-b376-16c4d4d4b749

module
public import Definitions.Def_BalanceSpecificaton_EntropyContinuity
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Definitions.Def_BalanceSpecificaton_BlockingEstimate
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_VariationalPrinciple
public import Theorems.Thm_BalanceSpecification_blockDistribution_finitePointProbability_representatives
public import Theorems.Thm_BalanceSpecification_FiniteEntropy_shannon_uniform
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_extensionPairs
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.cylinder_nil
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_extensionPairs
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter Set
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution (N : ℕ)
    [Nonempty ↥(wordFinset (language X) N)]
    (x : ↥(wordFinset (language X) N) → X.carrier)
    (hx : ∀ w, block (x w).val 0 N = w.val) :
    blockEntropy (finitePointProbability x) N = Real.log (wordCount (language X) N) := by
  rw [blockEntropy_eq_shannon]
  have hd : blockDistribution (finitePointProbability x) N =
      (fun _ : ↥(wordFinset (language X) N) => 1 / (Fintype.card ↥(wordFinset (language X) N) : ℝ)) := by
    funext w
    simpa only [Fintype.card_coe, wordCount] using
      blockDistribution_finitePointProbability_representatives N x hx w
  rw [hd, FiniteEntropy.shannon_uniform, Fintype.card_coe]
  rfl
end BalanceSpecification
