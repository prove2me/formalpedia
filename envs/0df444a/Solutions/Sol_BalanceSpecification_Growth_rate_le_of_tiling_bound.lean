-- Prove2me | solution 1 for BalanceSpecification.Growth.rate_le_of_tiling_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:38:32.976651+00:00
-- url     : https://prove2.me/submissions/2052d960-fbcf-46b0-9827-ec616a8e4957

module
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GrowthTiling
public import Theorems.Thm_BalanceSpecification_Growth_rate_le_log_div


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Set Filter
open scoped Topology
open BalanceSpecification BalanceSpecification.Growth
namespace BalanceSpecification.Growth
theorem _root_.solution {a : ℕ → ℝ} (ha : ∀ n, 1 ≤ a n)
    (hs : Submultiplicative a) {n : ℕ} (hn : 0 < n) {M : ℕ} {C B : ℝ}
    (hC : 0 < C) (hB : 0 < B)
    (hbound : ∀ k : ℕ, a (2 * M + k * n) ≤ C * B ^ k) :
    rate a ≤ Real.log B / n := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hlim := tendsto_add_mul_div_add_mul_atTop_nhds
    (Real.log C) ((2 * M : ℕ) : ℝ) (Real.log B) hnR
  apply ge_of_tendsto hlim
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  have hkn : 0 < k * n := Nat.mul_pos hk hn
  have hindex : 0 < 2 * M + k * n := by omega
  have hlog : Real.log (a (2 * M + k * n)) ≤ Real.log C + (k : ℝ) * Real.log B := by
    have H := Real.log_le_log (lt_of_lt_of_le zero_lt_one (ha _)) (hbound k)
    simpa only [Real.log_mul hC.ne' (pow_ne_zero _ hB.ne'), Real.log_pow] using H
  have hden : ((2 * M + k * n : ℕ) : ℝ) = ((2 * M : ℕ) : ℝ) + (n : ℝ) * k := by
    push_cast
    ring
  calc
    rate a ≤ Real.log (a (2 * M + k * n)) / (2 * M + k * n : ℕ) :=
      rate_le_log_div ha hs hindex.ne'
    _ ≤ (Real.log C + (k : ℝ) * Real.log B) / (2 * M + k * n : ℕ) :=
      div_le_div_of_nonneg_right hlog (Nat.cast_nonneg _)
    _ = (Real.log C + Real.log B * k) / (((2 * M : ℕ) : ℝ) + (n : ℝ) * k) := by
      rw [hden, mul_comm (k : ℝ)]
end BalanceSpecification.Growth
