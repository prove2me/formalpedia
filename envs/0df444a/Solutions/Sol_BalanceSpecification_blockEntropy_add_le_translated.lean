-- Prove2me | solution 1 for BalanceSpecification.blockEntropy_add_le_translated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:17:15.451004+00:00
-- url     : https://prove2.me/submissions/d543cde6-4aac-4339-8d1d-bb1fd24be13a

module
public import Definitions.Def_BalanceSpecificaton_EntropyContinuity
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Definitions.Def_BalanceSpecificaton_BlockingEstimate
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_VariationalPrinciple
public import Theorems.Thm_BalanceSpecification_translatedProbability_cylinder_real
public import Theorems.Thm_BalanceSpecification_FiniteEntropy_shannon_joint_le
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
theorem _root_.solution (μ : ProbabilityMeasure X.carrier) (m n : ℕ) :
    blockEntropy μ (m + n) ≤ blockEntropy μ m + blockEntropy (translatedProbability μ m) n := by
  have hcol (v : ↥(wordFinset (language X) n)) :
      ∑ u, jointBlockDistribution μ m n (u, v) =
        blockDistribution (translatedProbability μ m) n v := by
    calc
      _ = ∑ u ∈ wordFinset (language X) m,
          (μ : Measure X.carrier).real (cylinder X (u ++ v.val) 0) :=
        Finset.sum_coe_sort _ _
      _ = (μ : Measure X.carrier).real (cylinder X v.val (0 + (m : ℤ))) :=
        sum_cylinder_append_left μ v.val m 0
      _ = _ := by
        change _ = (translatedProbability μ m : Measure X.carrier).real (cylinder X v.val 0)
        rw [translatedProbability_cylinder_real, zero_add, add_zero]
  have h := FiniteEntropy.shannon_joint_le (p := jointBlockDistribution μ m n)
    (fun _ => measureReal_nonneg) (jointBlockDistribution_sum μ m n)
  simp only [jointBlockDistribution_row, hcol, shannon_jointBlockDistribution,
    ← blockEntropy_eq_shannon] at h
  exact h
end BalanceSpecification
