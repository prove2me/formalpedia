-- Prove2me | solution 1 for BalanceSpecification.continuous_probabilityReal_of_isClopen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:13:11.087591+00:00
-- url     : https://prove2.me/submissions/8de7d315-d4e9-4861-814c-95d201da2df9

module
public import Definitions.Def_BalanceSpecificaton_MaximalEntropy
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyContinuity
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
namespace BalanceSpecification
theorem _root_.solution
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    [HasOuterApproxClosed Ω] {E : Set Ω} (hE : IsClopen E) :
    Continuous (fun μ : ProbabilityMeasure Ω => (μ : Measure Ω).real E) := by
  rw [continuous_iff_continuousAt]
  intro μ
  change Tendsto (fun ν : ProbabilityMeasure Ω => (ν : Measure Ω).real E) (𝓝 μ)
    (𝓝 ((μ : Measure Ω).real E))
  have ht := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto
    (show Tendsto (fun ν : ProbabilityMeasure Ω => ν) (𝓝 μ) (𝓝 μ) from tendsto_id) hE
  simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn, Function.comp_def] using
    (NNReal.continuous_coe.tendsto (μ E)).comp ht
end BalanceSpecification
