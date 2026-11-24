-- Prove2me | solution 1 for BalanceSpecification.sGap_wordCount_le_uniform_pressure_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:53:51.422037+00:00
-- url     : https://prove2.me/submissions/42131551-b10c-4fb8-9ada-ad4f4022c0a7

module
public import Definitions.Def_BalanceSpecificaton_SGapEntropy
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapBSM
public import Theorems.Thm_BalanceSpecification_sGap_wordCount_le_restricted_renewal_sum
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
public import Theorems.Thm_BalanceSpecification_renewalCount_le_pow
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
    [TopologicalSpace Bool] [DiscreteTopology Bool] {S : Set ℕ} (hS : S.Nonempty)
    {β : ℝ} (hβ : 1 < β)
    (hpressure : ∀ F : Finset ℕ, (∀ s ∈ F, s ∈ S) → ∑ s ∈ F, (β⁻¹)^(s + 1) ≤ 1)
    (n : ℕ) :
    (wordCount (language (sGapShift S)) n : ℝ) ≤
      (1 + β⁻¹ * ((1 - β⁻¹)⁻¹)^2) * β^n := by
  classical
  have hβpos : 0 < β := zero_lt_one.trans hβ
  let q := β⁻¹
  have hq0 : 0 ≤ q := inv_nonneg.mpr hβpos.le
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ hβ
  have hsummable : Summable (fun i : ℕ => q^i) :=
    summable_geometric_of_norm_lt_one (by simpa only [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1)
  have hgeom : (∑ i ∈ Finset.range (n + 1), q^i) ≤ (1 - q)⁻¹ := by
    calc
      _ ≤ ∑' i : ℕ, q^i := hsummable.sum_le_tsum _ (fun _ _ => pow_nonneg hq0 _)
      _ = (1 - q)⁻¹ := tsum_geometric_of_lt_one hq0 hq1
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range (n + 1), q^i :=
    Finset.sum_nonneg (fun _ _ => pow_nonneg hq0 _)
  have hterm (a m : ℕ) :
      ((if a + m + 1 ≤ n then renewalCount S (n - a - m - 1) else 0 : ℕ) : ℝ) ≤
        β^n * q^(a + m + 1) := by
    by_cases ham : a + m + 1 ≤ n
    · simp only [if_pos ham, q]
      have hpow : β^(n - a - m - 1) = β^n * (β⁻¹)^(a + m + 1) := by
        rw [inv_pow, ← div_eq_mul_inv]
        apply (eq_div_iff (pow_ne_zero _ hβpos.ne')).mpr
        rw [← pow_add]
        congr 1
        omega
      exact (renewalCount_le_pow hβpos hpressure _).trans_eq hpow
    · simp only [if_neg ham, Nat.cast_zero]
      exact mul_nonneg (pow_nonneg hβpos.le _) (pow_nonneg hq0 _)
  have hraw : (wordCount (language (sGapShift S)) n : ℝ) ≤
      1 + ∑ a ∈ Finset.range (n + 1), ∑ m ∈ Finset.range (n + 1),
        ((if a + m + 1 ≤ n then renewalCount S (n - a - m - 1) else 0 : ℕ) : ℝ) := by
    exact_mod_cast sGap_wordCount_le_restricted_renewal_sum hS n
  have hsum : (∑ a ∈ Finset.range (n + 1), ∑ m ∈ Finset.range (n + 1),
      β^n * q^(a + m + 1)) =
      β^n * q * (∑ a ∈ Finset.range (n + 1), q^a)^2 := by
    calc
      _ = ∑ a ∈ Finset.range (n + 1), ∑ m ∈ Finset.range (n + 1),
          (β^n * q) * q^a * q^m := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro m hm
        rw [pow_add, pow_add, pow_one]
        ring
      _ = ((β^n * q) * (∑ a ∈ Finset.range (n + 1), q^a)) *
          (∑ m ∈ Finset.range (n + 1), q^m) := by
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ = _ := by ring

  have hsq : (∑ a ∈ Finset.range (n + 1), q^a)^2 ≤ ((1 - q)⁻¹)^2 :=
    pow_le_pow_left₀ hsum0 hgeom _
  calc
    (wordCount (language (sGapShift S)) n : ℝ) ≤
        1 + ∑ a ∈ Finset.range (n + 1), ∑ m ∈ Finset.range (n + 1), β^n * q^(a + m + 1) :=
      hraw.trans (add_le_add (le_refl 1) (Finset.sum_le_sum fun a ha =>
        Finset.sum_le_sum fun m hm => hterm a m))
    _ = 1 + β^n * q * (∑ a ∈ Finset.range (n + 1), q^a)^2 := by rw [hsum]
    _ ≤ β^n + β^n * q * ((1 - q)⁻¹)^2 :=
      add_le_add (one_le_pow₀ hβ.le)
        (mul_le_mul_of_nonneg_left hsq (mul_nonneg (pow_nonneg hβpos.le _) hq0))
    _ = (1 + β⁻¹ * ((1 - β⁻¹)⁻¹)^2) * β^n := by dsimp only [q]; ring
end BalanceSpecification
