-- Prove2me | solution 1 for BalanceSpecification.entropy_le_log_of_polynomial_wordCount_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:36:26.278713+00:00
-- url     : https://prove2.me/submissions/1061efb3-e4ff-4183-89d8-99de5b5ff1b0

module
public import Definitions.Def_BalanceSpecificaton_SGapRenewal
public import Definitions.Def_BalanceSpecificaton_GrowthUpperBounds
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapEntropy
public import Theorems.Thm_BalanceSpecification_exp_mul_entropy_le_wordCount
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
theorem _root_.solution
    {A : Type*} [Fintype A] [TopologicalSpace A] {X : ShiftSpace A}
    (hX : X.carrier.Nonempty) {β : ℝ} (hβ : 0 < β)
    (hupper : ∀ n : ℕ, (wordCount (language X) n : ℝ) ≤
      2 * ((n : ℝ) + 1)^2 * β^n) : entropy X hX ≤ Real.log β := by
  by_contra hnot
  have hgap : Real.log β < entropy X hX := lt_of_not_ge hnot
  let r := Real.exp (entropy X hX) / β
  have hr : 1 < r := by
    apply (one_lt_div hβ).mpr
    calc
      β = Real.exp (Real.log β) := (Real.exp_log hβ).symm
      _ < Real.exp (entropy X hX) := Real.exp_lt_exp.mpr hgap
  have hrpos : 0 < r := zero_lt_one.trans hr
  have hbound (n : ℕ) : r^n ≤ 2 * ((n : ℝ) + 1)^2 := by
    have hh := (exp_mul_entropy_le_wordCount hX n).trans (hupper n)
    have hh' := (div_le_iff₀ (pow_pos hβ n)).mpr hh
    simpa only [r, div_pow, Real.exp_nat_mul] using hh'
  have ht : Tendsto (fun n : ℕ => 2 * ((n : ℝ) + 1)^2 / r^n) atTop (𝓝 0) := by
    have hh := ((tendsto_pow_const_div_const_pow_of_one_lt 2 hr).comp
      (tendsto_add_atTop_nat 1)).mul_const (2 * r)
    convert hh using 1
    · funext n
      simp only [Function.comp_def, Nat.cast_add, Nat.cast_one, pow_succ]
      field_simp [hrpos.ne', pow_ne_zero _ hrpos.ne']
    · norm_num
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))).exists
  have hge : 1 ≤ 2 * ((n : ℝ) + 1)^2 / r^n :=
    (le_div_iff₀ (pow_pos hrpos n)).mpr (by simpa only [one_mul] using hbound n)
  exact (not_lt_of_ge hge) hn
end BalanceSpecification
