-- Prove2me | solution 1 for BalanceSpecification.log_le_sGap_entropy_of_pressure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:39:12.694019+00:00
-- url     : https://prove2.me/submissions/5bbd7432-2cd1-4509-90ef-12666cf8ff93

module
public import Definitions.Def_BalanceSpecificaton_SGapRenewal
public import Definitions.Def_BalanceSpecificaton_GrowthUpperBounds
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGapEntropy
public import Theorems.Thm_BalanceSpecification_sGap_partial_pressure_le_one_of_entropy_lt
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
public import Theorems.Thm_BalanceSpecification_sGapShift_nonempty
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
theorem _root_.solution [TopologicalSpace Bool] [DiscreteTopology Bool]
    {S : Set ℕ} (hS : S.Nonempty) {β : ℝ} (hβ : 1 < β)
    (hroot : HasSum (fun s : S => (β⁻¹)^(s.val + 1)) 1) :
    Real.log β ≤ entropy (sGapShift S) (sGapShift_nonempty hS) := by
  classical
  by_contra hnot
  have hgap : entropy (sGapShift S) (sGapShift_nonempty hS) < Real.log β := lt_of_not_ge hnot
  obtain ⟨α, hα, hαβ⟩ := exists_between hgap
  let γ := Real.exp α
  have hγ : 0 < γ := Real.exp_pos α
  have hβpos : 0 < β := zero_lt_one.trans hβ
  have hγβ : γ < β := by
    calc
      γ < Real.exp (Real.log β) := Real.exp_lt_exp.mpr hαβ
      _ = β := Real.exp_log hβpos
  have hInv : β⁻¹ < γ⁻¹ := by
    simpa only [one_div] using one_div_lt_one_div_of_lt hγ hγβ
  have hpart (G : Finset S) : ∑ s ∈ G, (γ⁻¹)^(s.val + 1) ≤ 1 := by
    have hF : ∀ s ∈ G.image Subtype.val, s ∈ S := by
      intro s hs
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hs
      exact t.property
    calc
      _ = ∑ s ∈ G.image Subtype.val, (γ⁻¹)^(s + 1) :=
        (Finset.sum_image (f := fun s : ℕ => (γ⁻¹)^(s + 1))
          (fun a ha b hb h => Subtype.ext h)).symm
      _ ≤ 1 := sGap_partial_pressure_le_one_of_entropy_lt hS hγ
        (by simpa only [γ, Real.log_exp] using hα) _ hF
  have hγsum : Summable (fun s : S => (γ⁻¹)^(s.val + 1)) :=
    summable_of_sum_le (fun _ => pow_nonneg (inv_nonneg.mpr hγ.le) _) hpart
  have hγle : (∑' s : S, (γ⁻¹)^(s.val + 1)) ≤ 1 := hγsum.tsum_le_of_sum_le hpart
  obtain ⟨s, hs⟩ := hS
  have hle (t : S) : (β⁻¹)^(t.val + 1) ≤ (γ⁻¹)^(t.val + 1) :=
    pow_le_pow_left₀ (inv_nonneg.mpr hβpos.le) hInv.le _
  have hstrict : (β⁻¹)^((⟨s, hs⟩ : S).val + 1) < (γ⁻¹)^((⟨s, hs⟩ : S).val + 1) :=
    pow_lt_pow_left₀ hInv (inv_nonneg.mpr hβpos.le) (Nat.succ_ne_zero s)
  have htsum := Summable.tsum_lt_tsum hle hstrict hroot.summable hγsum
  rw [hroot.tsum_eq] at htsum
  exact (not_lt_of_ge hγle) htsum
end BalanceSpecification
