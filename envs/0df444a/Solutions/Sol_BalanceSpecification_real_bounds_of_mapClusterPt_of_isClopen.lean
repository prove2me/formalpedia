-- Prove2me | solution 1 for BalanceSpecification.real_bounds_of_mapClusterPt_of_isClopen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:38:12.81486+00:00
-- url     : https://prove2.me/submissions/b9c4099a-6c0d-4ef4-bede-b4878071e578

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts
public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
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
namespace BalanceSpecification
theorem _root_.solution
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    [HasOuterApproxClosed Ω] {ν : ℕ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω}
    (hμ : MapClusterPt μ atTop ν) {E : Set Ω} (hE : IsClopen E) {l r : ℝ}
    (hb : ∀ᶠ n : ℕ in atTop, l ≤ (ν n : Measure Ω).real E ∧
      (ν n : Measure Ω).real E ≤ r) :
    l ≤ (μ : Measure Ω).real E ∧ (μ : Measure Ω).real E ≤ r := by
  obtain ⟨U, hU, hlim⟩ := mapClusterPt_iff_ultrafilter.mp hμ
  have ht := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hlim hE
  have htreal : Tendsto (fun n => (ν n : Measure Ω).real E) U (𝓝 ((μ : Measure Ω).real E)) := by
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn, Function.comp_def] using
      (NNReal.continuous_coe.tendsto (μ E)).comp ht
  exact ⟨ge_of_tendsto htreal ((hb.mono fun _ h => h.1).filter_mono hU),
    le_of_tendsto htreal ((hb.mono fun _ h => h.2).filter_mono hU)⟩
end BalanceSpecification
