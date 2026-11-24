-- Prove2me | solution 1 for BalanceSpecification.GibbsBounds.wordCount_exp_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:14:17.927902+00:00
-- url     : https://prove2.me/submissions/d101846f-8dd3-4ea3-b6da-a66ce4dc17db

module
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
public import Definitions.Def_BalanceSpecificaton_BlockEntropy
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsBalance
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
public import Theorems.Thm_BalanceSpecification_sum_cylinder_real_eq_one
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
namespace GibbsBounds
theorem _root_.solution {hX : X.carrier.Nonempty}
    {μ : ProbabilityMeasure X.carrier} {K : ℝ} (hG : GibbsBounds hX μ K) (n : ℕ) :
    (wordCount (language X) n : ℝ) ≤ K * Real.exp ((n : ℝ) * entropy X hX) := by
  have H : (wordCount (language X) n : ℝ) / K ≤
      Real.exp ((n : ℝ) * entropy X hX) := by
    calc
      (wordCount (language X) n : ℝ) / K =
          ∑ _w ∈ wordFinset (language X) n, 1 / K := by
        simp only [Finset.sum_const, nsmul_eq_mul, wordCount]
        ring
      _ ≤ ∑ w ∈ wordFinset (language X) n,
          (μ : Measure X.carrier).real (cylinder X w 0) *
            Real.exp ((n : ℝ) * entropy X hX) := by
        apply Finset.sum_le_sum
        intro w hw
        obtain ⟨hwL, hwlen⟩ := mem_wordFinset.mp hw
        simpa only [hwlen] using (hG.2 w hwL).1
      _ = Real.exp ((n : ℝ) * entropy X hX) := by
        rw [← Finset.sum_mul, sum_cylinder_real_eq_one, one_mul]
  simpa only [mul_comm] using (div_le_iff₀ hG.1).mp H
end GibbsBounds
end BalanceSpecification
