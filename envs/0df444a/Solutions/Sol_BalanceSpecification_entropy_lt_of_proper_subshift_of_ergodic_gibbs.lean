-- Prove2me | solution 1 for BalanceSpecification.entropy_lt_of_proper_subshift_of_ergodic_gibbs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:15:55.434948+00:00
-- url     : https://prove2.me/submissions/d56cbc81-2149-4476-bde5-96ebd3c8a865

module
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Definitions.Def_BalanceSpecificaton_EntropyMinimal
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsEntropyMinimal
public import Theorems.Thm_BalanceSpecification_GibbsBounds_subshift_real_pos_of_entropy_eq
public import Theorems.Thm_BalanceSpecification_GibbsBounds_cylinder_real_pos
public import Theorems.Thm_BalanceSpecification_IsGibbsMeasure_cylinder_real_pos
public import Theorems.Thm_BalanceSpecification_carrier_subset_of_language_subset
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_entropy_mono
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_measurableSet_cylinder
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
theorem _root_.solution
    {X : ShiftSpace A} (hX : X.carrier.Nonempty)
    {μ : ProbabilityMeasure X.carrier} (hG : IsGibbsMeasure hX μ)
    (hErg : Ergodic (shiftMap X) (μ : Measure X.carrier))
    {Y : ShiftSpace A} (hY : Y.carrier.Nonempty) (hproper : Y.carrier ⊂ X.carrier) :
    entropy Y hY < entropy X hX := by
  have hle := entropy_mono hY hX hproper.subset
  by_contra hnot
  have heq : entropy Y hY = entropy X hX := le_antisymm hle (le_of_not_gt hnot)
  let S : Set X.carrier := {x | x.val ∈ Y.carrier}
  have hSmeas : MeasurableSet S := (Y.isClosed.preimage continuous_subtype_val).measurableSet
  have hSinv : shiftMap X ⁻¹' S = S := by
    ext x
    constructor
    · intro hx
      have H := Y.mapsTo (-1) hx
      change SymbolicDynamics.FullShift.shift (-1)
        (SymbolicDynamics.FullShift.shift 1 x.val) ∈ Y.carrier at H
      have he : SymbolicDynamics.FullShift.shift (-1)
          (SymbolicDynamics.FullShift.shift 1 x.val) = x.val := by
        funext i
        simp only [SymbolicDynamics.FullShift.shift_apply, add_neg_cancel_left]
      change x.val ∈ Y.carrier
      simpa only [he] using H
    · intro hx
      exact Y.mapsTo 1 hx
  obtain ⟨K, hB⟩ := hG.2
  have hSpos : 0 < (μ : Measure X.carrier).real S :=
    hB.subshift_real_pos_of_entropy_eq hY hG.1 hproper.subset heq
  have hnotSubset : ¬ language X ⊆ language Y := by
    intro h
    exact hproper.not_subset (carrier_subset_of_language_subset h)
  obtain ⟨w, hwX, hwY⟩ := Set.not_subset.mp hnotSubset
  have hdisj : S ⊆ (cylinder X w 0)ᶜ := by
    intro x hx hc
    exact hwY ⟨x.val, hx, 0, hc⟩
  have hSlt : (μ : Measure X.carrier).real S < 1 := by
    have H := measureReal_mono (μ := (μ : Measure X.carrier)) hdisj
    rw [probReal_compl_eq_one_sub (measurableSet_cylinder X w 0)] at H
    have hp := hB.cylinder_real_pos hwX
    linarith only [H, hp]
  have hzeroone := hErg.toPreErgodic.prob_eq_zero_or_one hSmeas hSinv
  rcases hzeroone with hz | ho
  · have H : (μ : Measure X.carrier).real S = 0 := by
      simp only [measureReal_def, hz, ENNReal.toReal_zero]
    linarith only [H, hSpos]
  · have H : (μ : Measure X.carrier).real S = 1 := by
      simp only [measureReal_def, ho, ENNReal.toReal_one]
    linarith only [H, hSlt]
end BalanceSpecification
