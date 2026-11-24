-- Prove2me | solution 1 for BalanceSpecification.blocking_estimate_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:38:59.943172+00:00
-- url     : https://prove2.me/submissions/310c3cc5-fc34-46b2-a83a-d14e1e84fa3c

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_BlockingEstimate
public import Theorems.Thm_BalanceSpecification_sum_offset_blocks_le
public import Theorems.Thm_BalanceSpecification_block_prefix_tiles_suffix_le
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_wordFinset



set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {H : ℕ → ℕ → ℝ}
namespace BalanceSpecification
theorem _root_.solution {C : ℝ} (hC : 0 ≤ C)
    (hnonneg : ∀ s l, 0 ≤ H s l)
    (hsub : ∀ s a b, H s (a + b) ≤ H s a + H (s + a) b)
    (hbound : ∀ s l, H s l ≤ (l : ℝ) * C)
    {n N : ℕ} (hn : 0 < n) (hN : n ≤ N) :
    (n : ℝ) * H 0 N ≤ (∑ i ∈ Finset.range N, H i n) + 2 * (n : ℝ)^2 * C := by
  have hzero : ∀ s, H s 0 = 0 := by
    intro s
    have hu := hbound s 0
    simp only [Nat.cast_zero, zero_mul] at hu
    exact le_antisymm hu (hnonneg s 0)
  let q := N / n
  let k := q - 1
  have hq : 1 ≤ q := by
    exact (Nat.le_div_iff_mul_le hn).mpr (by simpa only [one_mul] using hN)
  have hqn : q = k + 1 := by dsimp only [k]; omega
  have hdecomp : N = k * n + n + N % n := by
    have hd := Nat.mod_add_div N n
    change N % n + n * q = N at hd
    rw [hqn, Nat.mul_add, mul_one, Nat.mul_comm n k] at hd
    omega
  have hrem : N % n < n := Nat.mod_lt N hn
  have hkn : k * n ≤ N := by omega
  have hoffset : ∀ r ∈ Finset.range n,
      H 0 N ≤ (∑ j ∈ Finset.range k, H (r + j * n) n) + 2 * (n : ℝ) * C := by
    intro r hr
    have hrn := Finset.mem_range.mp hr
    have hfit : r + k * n ≤ N := by omega
    have h := block_prefix_tiles_suffix_le hzero hsub hfit
    have hp := hbound 0 r
    have hs := hbound (r + k * n) (N - (r + k * n))
    have hboundary : r + (N - (r + k * n)) ≤ 2 * n := by omega
    have hboundary' : (r : ℝ) + (N - (r + k * n) : ℕ) ≤ 2 * (n : ℝ) := by
      exact_mod_cast hboundary
    have hscale := mul_le_mul_of_nonneg_right hboundary' hC
    nlinarith only [h, hp, hs, hscale]
  have hsum := Finset.sum_le_sum hoffset
  have havg : (n : ℝ) * H 0 N ≤
      (∑ r ∈ Finset.range n, ∑ j ∈ Finset.range k, H (r + j * n) n) +
        2 * (n : ℝ)^2 * C := by
    have hsum' : (n : ℝ) * H 0 N ≤
        (∑ r ∈ Finset.range n, ∑ j ∈ Finset.range k, H (r + j * n) n) +
          (n : ℝ) * (2 * (n : ℝ) * C) := by
      simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Finset.sum_add_distrib] using hsum
    convert hsum' using 1
    ring
  exact havg.trans (add_le_add (sum_offset_blocks_le hnonneg hn hkn) le_rfl)
end BalanceSpecification
