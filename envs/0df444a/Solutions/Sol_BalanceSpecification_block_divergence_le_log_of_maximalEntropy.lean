-- Prove2me | solution 1 for BalanceSpecification.block_divergence_le_log_of_maximalEntropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:15:37.618704+00:00
-- url     : https://prove2.me/submissions/d3136e88-e24c-4458-9ad5-3491c20a583b

module
public import Definitions.Def_BalanceSpecificaton_MaximalEntropy
public import Definitions.Def_BalanceSpecificaton_AbsoluteContinuity
public import Definitions.Def_BalanceSpecificaton_GibbsErgodic
public import Mathlib.Dynamics.Ergodic.Extreme
public import Definitions.Def_BalanceSpecificaton_IntrinsicErgodicity
public import Theorems.Thm_BalanceSpecification_FiniteEntropy_divergence_le_log_of_gibbs_bound
public import Theorems.Thm_BalanceSpecification_GibbsBounds_cylinder_real_exp_bounds
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
public import Theorems.Thm_BalanceSpecification_mul_measureEntropy_le_blockEntropy
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
open BalanceSpecification
open MeasureTheory
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution {hX : X.carrier.Nonempty}
    {μ ν : ProbabilityMeasure X.carrier} {K : ℝ} (hB : GibbsBounds hX μ K)
    (hν : IsMaximalEntropyMeasure hX ν) (n : ℕ) :
    FiniteEntropy.divergence (blockDistribution ν n) (blockDistribution μ n) ≤ Real.log K := by
  obtain ⟨hInv, hEntropy⟩ := hν
  apply FiniteEntropy.divergence_le_log_of_gibbs_bound
    (fun _ => measureReal_nonneg) (blockDistribution_sum ν n) hB.1
    (t := (n : ℝ) * entropy X hX)
  · intro w
    have h := (hB.cylinder_real_exp_bounds (mem_wordFinset.mp w.property).1).1
    simpa only [blockDistribution, (mem_wordFinset.mp w.property).2] using h
  · change (n : ℝ) * entropy X hX ≤ FiniteEntropy.shannon (blockDistribution ν n)
    rw [← blockEntropy_eq_shannon]
    simpa only [hEntropy] using mul_measureEntropy_le_blockEntropy hInv n
end BalanceSpecification
