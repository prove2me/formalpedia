-- Prove2me | solution 1 for BalanceSpecification.exists_sGap_pressure_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:53:49.12993+00:00
-- url     : https://prove2.me/submissions/4af29fe7-4e87-4035-80f4-b6356837f074

module
public import Definitions.Def_BalanceSpecificaton_SGapEntropy
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapBSM
public import Theorems.Thm_BalanceSpecification_summable_sGap_pressure
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_renewalFinset
public import Theorems.Thm_BalanceSpecification_mem_renewalGaps
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_nil_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_periodicConfiguration_shift
public import Theorems.Thm_BalanceSpecification_renewalCount_zero
public import Theorems.Thm_BalanceSpecification_sGapListConcat_cons
public import Theorems.Thm_BalanceSpecification_sGapListConcat_nil
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_renewalFinset
attribute [local simp] BalanceSpecification.mem_renewalGaps
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.nil_mem_generatedWords
attribute [local simp] BalanceSpecification.periodicConfiguration_shift
attribute [local simp] BalanceSpecification.renewalCount_zero
attribute [local simp] BalanceSpecification.sGapListConcat_cons
attribute [local simp] BalanceSpecification.sGapListConcat_nil
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter Set
open scoped Topology
namespace BalanceSpecification
theorem _root_.solution {S : Set ℕ} {a b : ℕ}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    ∃ β : ℝ, 1 < β ∧ HasSum (fun s : S => (β⁻¹)^(s.val + 1)) 1 := by
  classical
  let P : ℝ → ℝ := fun q => ∑' s : S, q^(s.val + 1)
  have htwo : Continuous (fun q : ℝ => q^(a + 1) + q^(b + 1)) :=
    (continuous_id.pow _).add (continuous_id.pow _)
  have hnear2 : ∀ᶠ q : ℝ in 𝓝 1, 1 < q^(a + 1) + q^(b + 1) :=
    (htwo.tendsto (1 : ℝ)).eventually
      (lt_mem_nhds (show (1 : ℝ) < (1 : ℝ)^(a + 1) + (1 : ℝ)^(b + 1) by norm_num))
  have hnear : ∀ᶠ q : ℝ in 𝓝 1, 0 < q ∧ 1 < q^(a + 1) + q^(b + 1) :=
    (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).and hnear2
  obtain ⟨q0, hq01, hq00, hq0two⟩ := hnear.exists_lt
  have hsum0 := summable_sGap_pressure (S := S) hq00.le hq01
  have hP0 : P 0 = 0 := by simp only [P, zero_pow (Nat.succ_ne_zero _), tsum_zero]
  have hab' : (⟨a, ha⟩ : S) ≠ ⟨b, hb⟩ := by
    intro heq
    exact hab (congrArg Subtype.val heq)
  have hPq0 : 1 < P q0 := by
    have hh := hsum0.sum_le_tsum ({⟨a, ha⟩, ⟨b, hb⟩} : Finset S)
      (fun _ _ => pow_nonneg hq00.le _)
    have htwole : q0^(a + 1) + q0^(b + 1) ≤ P q0 := by
      simpa only [Finset.sum_pair hab', P] using hh
    exact hq0two.trans_le htwole
  have hcont : ContinuousOn P (Icc 0 q0) := by
    apply continuousOn_tsum
      (fun s : S => (continuous_id.pow (s.val + 1)).continuousOn) hsum0
    intro s q hq
    change ‖q^(s.val + 1)‖ ≤ q0^(s.val + 1)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq.1 _)]
    exact pow_le_pow_left₀ hq.1 hq.2 _
  obtain ⟨q, hqI, hPq⟩ := intermediate_value_Icc hq00.le hcont
    (show (1 : ℝ) ∈ Icc (P 0) (P q0) from ⟨by rw [hP0]; norm_num, hPq0.le⟩)
  have hqpos : 0 < q := by
    rcases eq_or_lt_of_le hqI.1 with hzero | hpos
    · rw [← hzero, hP0] at hPq
      exact False.elim (zero_ne_one hPq)
    · exact hpos
  have hqone : q < 1 := hqI.2.trans_lt hq01
  have hpsum : HasSum (fun s : S => q^(s.val + 1)) 1 := by
    have hh := (summable_sGap_pressure (S := S) hqpos.le hqone).hasSum
    simpa only [P, hPq] using hh
  refine ⟨q⁻¹, ?_, ?_⟩
  · simpa only [one_div] using (one_lt_div hqpos).mpr hqone
  · simpa only [inv_inv] using hpsum
end BalanceSpecification
