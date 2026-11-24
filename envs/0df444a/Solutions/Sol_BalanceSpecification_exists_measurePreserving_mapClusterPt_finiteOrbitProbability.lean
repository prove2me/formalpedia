-- Prove2me | solution 1 for BalanceSpecification.exists_measurePreserving_mapClusterPt_finiteOrbitProbability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:41:57.079818+00:00
-- url     : https://prove2.me/submissions/2602d66f-c6c2-4e33-9a8b-d3720c704361

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts
public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
public import Theorems.Thm_BalanceSpecification_measurePreserving_of_mapClusterPt_finiteOrbitProbability
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
open MeasureTheory Filter
open scoped Topology ENNReal Classical BoundedContinuousFunction
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [T2Space Ω]
    [HasOuterApproxClosed Ω]
    {I : ℕ → Type*} [∀ n, Fintype (I n)] [∀ n, Nonempty (I n)]
namespace BalanceSpecification
theorem _root_.solution
    [CompactSpace Ω] {f : Ω → Ω} (hf : Continuous f)
    (x : ∀ n, I n → Ω) :
    ∃ μ : ProbabilityMeasure Ω,
      MapClusterPt μ atTop (fun n => finiteOrbitProbability f (x n) n) ∧
        MeasurePreserving f (μ : Measure Ω) (μ : Measure Ω) := by
  obtain ⟨μ, _, hμ⟩ := isCompact_univ.exists_mapClusterPt
    (u := fun n => finiteOrbitProbability f (x n) n) (f := atTop) (by simp)
  exact ⟨μ, hμ, measurePreserving_of_mapClusterPt_finiteOrbitProbability hf x hμ⟩
end BalanceSpecification
