-- Prove2me | solution 1 for BalanceSpecification.GibbsBounds.subshift_real_pos_of_entropy_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:14:56.473719+00:00
-- url     : https://prove2.me/submissions/a9f22af9-e7e3-4b01-87c5-75330b070d94

module
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Definitions.Def_BalanceSpecificaton_EntropyMinimal
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsEntropyMinimal
public import Theorems.Thm_BalanceSpecification_subshiftCylinderEvent_antitone
public import Theorems.Thm_BalanceSpecification_iInter_subshiftCylinderEvent
public import Theorems.Thm_BalanceSpecification_measurableSet_subshiftCylinderEvent
public import Theorems.Thm_BalanceSpecification_GibbsBounds_subshiftCylinderEvent_lower_of_entropy_eq
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_avoidingLanguage
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_languageShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.cylinder_nil
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_avoidingLanguage
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_languageShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A]
variable [Fintype A]
variable [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A]
namespace BalanceSpecification
namespace GibbsBounds
theorem _root_.solution
    {X Y : ShiftSpace A} {hX : X.carrier.Nonempty} (hY : Y.carrier.Nonempty)
    {μ : ProbabilityMeasure X.carrier} {K : ℝ} (hB : GibbsBounds hX μ K)
    (hμ : IsInvariant μ) (hYX : Y.carrier ⊆ X.carrier)
    (heq : entropy Y hY = entropy X hX) :
    0 < (μ : Measure X.carrier).real {x : X.carrier | x.val ∈ Y.carrier} := by
  have ht := tendsto_measure_iInter_atTop
    (fun n => (measurableSet_subshiftCylinderEvent X Y n).nullMeasurableSet)
    (subshiftCylinderEvent_antitone X Y)
    (⟨0, measure_ne_top (μ : Measure X.carrier) _⟩)
  have ht' := (ENNReal.tendsto_toReal
    (measure_ne_top (μ : Measure X.carrier) (⋂ n, subshiftCylinderEvent X Y n))).comp ht
  have hlim : Tendsto (fun n => (μ : Measure X.carrier).real (subshiftCylinderEvent X Y n))
      atTop (𝓝 ((μ : Measure X.carrier).real {x : X.carrier | x.val ∈ Y.carrier})) := by
    simpa only [Function.comp_def, measureReal_def, iInter_subshiftCylinderEvent] using ht'
  exact (div_pos zero_lt_one hB.1).trans_le
    (ge_of_tendsto' hlim (fun n => hB.subshiftCylinderEvent_lower_of_entropy_eq hY hμ hYX heq n))
end GibbsBounds
end BalanceSpecification
