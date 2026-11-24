-- Prove2me | solution 1 for BalanceSpecification.Growth.exists_exp_bound_of_rate_lt_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:36:03.464809+00:00
-- url     : https://prove2.me/submissions/e51ed909-f544-4f45-8df3-e3e57700cb0d

module
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GrowthUpperBounds
public import Theorems.Thm_BalanceSpecification_Growth_tendsto_rate
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification BalanceSpecification.Growth
namespace BalanceSpecification.Growth
theorem _root_.solution {a : ℕ → ℝ} (ha : ∀ n, 1 ≤ a n)
    (hs : Submultiplicative a) {γ : ℝ} (hγ : 0 < γ)
    (hgap : rate a < Real.log γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, a n ≤ C * γ ^ n := by
  have hev := (tendsto_rate ha hs).eventually (gt_mem_nhds hgap)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hev.and (eventually_gt_atTop (0 : ℕ)))
  let C : ℝ := max 1 (∑ i ∈ Finset.range N, a i / γ ^ i)
  have hC1 : 1 ≤ C := le_max_left _ _
  refine ⟨C, zero_lt_one.trans_le hC1, ?_⟩
  intro n
  by_cases hn : n < N
  · have hratio : a n / γ ^ n ≤ C :=
      (Finset.single_le_sum (f := fun i => a i / γ ^ i) (fun i _ => div_nonneg (zero_le_one.trans (ha i))
        (pow_nonneg hγ.le _)) (Finset.mem_range.mpr hn)).trans (le_max_right _ _)
    exact (div_le_iff₀ (pow_pos hγ n)).mp hratio
  · obtain ⟨hlog, hnpos⟩ := hN n (by omega)
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
    have hlog' : Real.log (a n) < Real.log (γ ^ n) := by
      rw [Real.log_pow]
      simpa only [mul_comm] using (div_lt_iff₀ hnR).mp hlog
    have hpow : a n ≤ γ ^ n :=
      ((Real.log_lt_log_iff (zero_lt_one.trans_le (ha n)) (pow_pos hγ n)).mp hlog').le
    exact hpow.trans (le_mul_of_one_le_left (pow_nonneg hγ.le _) hC1)
end BalanceSpecification.Growth
