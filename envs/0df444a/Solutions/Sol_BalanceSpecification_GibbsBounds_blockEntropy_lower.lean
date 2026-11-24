-- Prove2me | solution 1 for BalanceSpecification.GibbsBounds.blockEntropy_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:13:08.761056+00:00
-- url     : https://prove2.me/submissions/523dab0b-3cb2-4d28-8555-d667b57a010d

module
public import Definitions.Def_BalanceSpecificaton_BlockEntropy
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MaximalEntropy
public import Theorems.Thm_BalanceSpecification_GibbsBounds_cylinder_real_exp_bounds
public import Theorems.Thm_BalanceSpecification_GibbsBounds_cylinder_real_pos
public import Theorems.Thm_BalanceSpecification_IsGibbsMeasure_cylinder_real_pos
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
open MeasureTheory Filter
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
namespace GibbsBounds
theorem _root_.solution {hX : X.carrier.Nonempty}
    {μ : ProbabilityMeasure X.carrier} {K : ℝ} (hB : GibbsBounds hX μ K) (n : ℕ) :
    (n : ℝ) * entropy X hX - Real.log K ≤ blockEntropy μ n := by
  let t := (n : ℝ) * entropy X hX - Real.log K
  let p : Word A → ℝ := fun w => (μ : Measure X.carrier).real (cylinder X w 0)
  have hweight : ∀ w ∈ wordFinset (language X) n,
      p w * t ≤ -(p w) * Real.log (p w) := by
    intro w hw
    obtain ⟨hwL, hwlen⟩ := mem_wordFinset.mp hw
    have hp := hB.cylinder_real_pos hwL
    have hu := (hB.cylinder_real_exp_bounds hwL).2
    have hlog := Real.log_le_log hp hu
    rw [Real.log_mul hB.1.ne' (Real.exp_pos _).ne', Real.log_exp, hwlen] at hlog
    have ht : t ≤ -Real.log (p w) := by
      dsimp only [t, p]
      linarith only [hlog]
    simpa only [mul_neg, neg_mul] using mul_le_mul_of_nonneg_left ht
      (show 0 ≤ p w from measureReal_nonneg)
  calc
    _ = (∑ w ∈ wordFinset (language X) n, p w) * t := by
      rw [show (∑ w ∈ wordFinset (language X) n, p w) = 1 from
        sum_cylinder_real_eq_one X μ n 0, one_mul]
    _ = ∑ w ∈ wordFinset (language X) n, p w * t := Finset.sum_mul _ _ _
    _ ≤ blockEntropy μ n := Finset.sum_le_sum hweight
end GibbsBounds
end BalanceSpecification
