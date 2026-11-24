-- Prove2me | solution 1 for BalanceSpecification.biBalanced_of_isGibbsMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:15:44.718572+00:00
-- url     : https://prove2.me/submissions/9df606b6-9bbb-4f20-8cdc-e5d5ececc17b

module
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
public import Definitions.Def_BalanceSpecificaton_BlockEntropy
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsBalance
public import Theorems.Thm_BalanceSpecification_GibbsBounds_wordCount_exp_upper
public import Theorems.Thm_BalanceSpecification_GibbsBounds_extension_card_exp_lower
public import Theorems.Thm_BalanceSpecification_sum_follower_cylinder
public import Theorems.Thm_BalanceSpecification_sum_predecessor_cylinder
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
public import Theorems.Thm_BalanceSpecification_wordCount_pos_of_nonempty
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
open MeasureTheory
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution {hX : X.carrier.Nonempty}
    {μ : ProbabilityMeasure X.carrier} (hG : IsGibbsMeasure hX μ) :
    BiBalanced (language X) := by
  obtain ⟨K, hK⟩ := hG.2
  have hK3 : 0 < K ^ 3 := pow_pos hK.1 3
  have hcount (n : ℕ) : (0 : ℝ) < wordCount (language X) n := by
    exact_mod_cast wordCount_pos_of_nonempty hX n
  constructor
  · refine ⟨1 / K ^ 3, div_pos zero_lt_one hK3, ?_⟩
    intro u hu n _hn
    have H := hK.extension_card_exp_lower hu n (followerFinset (language X) u n)
      (fun w => u ++ w) (by
        intro w hw
        obtain ⟨_, hwlen, huw⟩ := mem_followerFinset.mp hw
        exact ⟨huw, by simp only [List.length_append, hwlen]⟩)
      (sum_follower_cylinder μ u n)
    have HB := (hK.wordCount_exp_upper n).trans (mul_le_mul_of_nonneg_left H hK.1.le)
    apply (div_le_div_iff₀ hK3 (hcount n)).mpr
    simpa only [one_mul, pow_succ, pow_zero, mul_one, mul_comm, mul_left_comm,
      mul_assoc] using HB
  · refine ⟨1 / K ^ 3, div_pos zero_lt_one hK3, ?_⟩
    intro u hu n _hn
    have H := hK.extension_card_exp_lower hu n (predecessorFinset (language X) u n)
      (fun w => w ++ u) (by
        intro w hw
        obtain ⟨_, hwlen, hwu⟩ := mem_predecessorFinset.mp hw
        exact ⟨hwu, by simp only [List.length_append, hwlen]; omega⟩)
      (sum_predecessor_cylinder hG.1 u n)
    have HB := (hK.wordCount_exp_upper n).trans (mul_le_mul_of_nonneg_left H hK.1.le)
    apply (div_le_div_iff₀ hK3 (hcount n)).mpr
    simpa only [one_mul, pow_succ, pow_zero, mul_one, mul_comm, mul_left_comm,
      mul_assoc] using HB
end BalanceSpecification
