-- Prove2me | solution 1 for BalanceSpecification.real_cylinderUnion_inter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:51:52.077139+00:00
-- url     : https://prove2.me/submissions/4ca776e2-ca44-40c4-81c3-a57ca061fae1

module
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsErgodic
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_disjoint_cylinder
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_measurableSet_cylinder
public import Theorems.Thm_BalanceSpecification_mem_allWords
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
open MeasureTheory Set
open scoped symmDiff ENNReal
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A] [Fintype A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A]
namespace BalanceSpecification
theorem _root_.solution {X : ShiftSpace A} (μ : Measure X.carrier)
    [IsFiniteMeasure μ] (S : Finset (Word A)) (l : ℕ)
    (hlen : ∀ a ∈ S, a.length = l) (k : ℤ) (C : Set X.carrier)
    (hC : MeasurableSet C) :
    μ.real ((⋃ a ∈ S, cylinder X a k) ∩ C) =
      ∑ a ∈ S, μ.real (cylinder X a k ∩ C) := by
  have hd : Set.PairwiseDisjoint (S : Set (Word A))
      (fun a => cylinder X a k ∩ C) := by
    intro a ha b hb hab
    exact (disjoint_cylinder X ((hlen a ha).trans (hlen b hb).symm) hab k).mono
      Set.inter_subset_left Set.inter_subset_left
  simpa only [Set.iUnion_inter] using
    (measureReal_biUnion_finset hd (fun a _ => (measurableSet_cylinder X a k).inter hC)
      (μ := μ))
end BalanceSpecification
