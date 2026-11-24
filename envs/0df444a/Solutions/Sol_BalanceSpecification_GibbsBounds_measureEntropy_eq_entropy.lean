-- Prove2me | solution 1 for BalanceSpecification.GibbsBounds.measureEntropy_eq_entropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:14:23.54686+00:00
-- url     : https://prove2.me/submissions/d3872e3f-da54-470e-ab72-b58f80871d1e

module
public import Definitions.Def_BalanceSpecificaton_BlockEntropy
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MaximalEntropy
public import Theorems.Thm_BalanceSpecification_GibbsBounds_blockEntropy_lower
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_measureEntropy_le_entropy
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_extensionPairs
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_tendsto_measureEntropy
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
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
namespace GibbsBounds
theorem _root_.solution {hX : X.carrier.Nonempty}
    {μ : ProbabilityMeasure X.carrier} {K : ℝ} (hB : GibbsBounds hX μ K)
    (hInv : IsInvariant μ) : measureEntropy μ hInv = entropy X hX := by
  apply le_antisymm (measureEntropy_le_entropy hX hInv)
  have hleft : Tendsto (fun n : ℕ => entropy X hX - Real.log K / n)
      atTop (𝓝 (entropy X hX)) := by
    simpa only [sub_zero] using
      tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (Real.log K))
  apply le_of_tendsto_of_tendsto hleft (tendsto_measureEntropy hInv)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnp : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_one.trans_le hn)
  have h := div_le_div_of_nonneg_right (hB.blockEntropy_lower n) hnp.le
  simpa only [sub_div, mul_div_cancel_left₀ _ hnp.ne'] using h
end GibbsBounds
end BalanceSpecification
