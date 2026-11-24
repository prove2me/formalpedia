-- Prove2me | solution 1 for DeletedPrimes.good_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:10:02.33002+00:00
-- url     : https://prove2.me/submissions/27edc7eb-b20e-426c-979d-ab3240cd7a54

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_GoodScales
import Theorems.Thm_DeletedPrimes_two_pow_rpow
import Theorems.Thm_DeletedPrimes_mertensSum_sub
import Theorems.Thm_DeletedPrimes_mem_mertens_sdiff
import Theorems.Thm_DeletedPrimes_tendsto_mertens_comp
import Theorems.Thm_DeletedPrimes_tendsto_log_rpow_div
import Theorems.Thm_DeletedPrimes_tendsto_log_two_mul_div
import Theorems.Thm_DeletedPrimes_log_two_bounds
import Theorems.Thm_DeletedPrimes_term_le

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution {S : Set ℕ} {α m : ℝ} (hα : 0 < α) (hm : 0 < m)
    (hM : MertensLaw S α m) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, ∃ j : ℕ, X ≤ 2 ^ j ∧ (2 : ℝ) ^ j ≤ X ^ (1 + δ) ∧
      ((2 : ℝ) ^ j) ^ (α - ε) ≤ blockCount S (2 ^ j) := by
  have hr0 : 0 ≤ (2 : ℝ) ^ (-ε) := by positivity
  have hr1 : (2 : ℝ) ^ (-ε) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have ht0 : ∀ j : ℕ, 0 ≤ Real.log 2 * (((j : ℝ) + 1) * ((2 : ℝ) ^ (-ε)) ^ j) :=
    fun j => mul_nonneg hl2 (by positivity)
  have htsum : Summable fun j : ℕ => Real.log 2 * (((j : ℝ) + 1) * ((2 : ℝ) ^ (-ε)) ^ j) := by
    have h1 : Summable fun n : ℕ => (n : ℝ) ^ 1 * ((2 : ℝ) ^ (-ε)) ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one 1
        (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
    have h2 := summable_geometric_of_lt_one hr0 hr1
    refine ((h1.add h2).mul_left (Real.log 2)).congr fun j => ?_
    simp only [pow_one]
    ring
  set T := ∑' j : ℕ, Real.log 2 * (((j : ℝ) + 1) * ((2 : ℝ) ^ (-ε)) ^ j) with hT
  have hT0 : 0 ≤ T := tsum_nonneg ht0
  have hinc : Tendsto (fun X => (mertensSum S α (X ^ (1 + δ)) - mertensSum S α (2 * X)) /
      Real.log X) atTop (𝓝 (m * (1 + δ) - m * 1)) := by
    have hA := tendsto_mertens_comp hM (tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 + δ))
      (tendsto_log_rpow_div (1 + δ))
    have hB := tendsto_mertens_comp hM (tendsto_id.const_mul_atTop two_pos)
      tendsto_log_two_mul_div
    exact (hA.sub hB).congr fun X => (sub_div _ _ _).symm
  have hpos : m * δ / 2 < m * (1 + δ) - m * 1 := by nlinarith
  filter_upwards [hinc.eventually (lt_mem_nhds hpos),
    Real.tendsto_log_atTop.eventually_gt_atTop (2 * T / (m * δ)), eventually_gt_atTop 1,
    (tendsto_rpow_atTop hδ).eventually_ge_atTop 2] with X hX1 hX2 hX3 hX4
  have hX0 : 0 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos hX3
  have h2X : 2 * X ≤ X ^ (1 + δ) := by
    rw [Real.rpow_add hX0, Real.rpow_one]; nlinarith
  have hlow : m * δ / 2 * Real.log X < mertensSum S α (X ^ (1 + δ)) - mertensSum S α (2 * X) := by
    rwa [lt_div_iff₀ hlog] at hX1
  have hTlt : T < m * δ / 2 * Real.log X := by
    rw [div_lt_iff₀ (by positivity)] at hX2
    linarith
  by_contra hcon
  push Not at hcon
  set D := (Finset.Icc 1 ⌊X ^ (1 + δ)⌋₊).filter (· ∈ S) \ (Finset.Icc 1 ⌊2 * X⌋₊).filter (· ∈ S)
    with hD
  have hup : mertensSum S α (X ^ (1 + δ)) - mertensSum S α (2 * X) ≤ T := by
    rw [mertensSum_sub S α h2X, ← Finset.sum_fiberwise_of_maps_to
      (fun p hp => Finset.mem_image_of_mem (Nat.log 2) hp)]
    calc _ ≤ ∑ j ∈ D.image (Nat.log 2),
          Real.log 2 * (((j : ℝ) + 1) * ((2 : ℝ) ^ (-ε)) ^ j) := by
          apply Finset.sum_le_sum
          intro j hj
          obtain ⟨p₀, hp₀, hpj⟩ := Finset.mem_image.mp hj
          obtain ⟨-, hp₀1, hp₀2, hp₀3⟩ := mem_mertens_sdiff (by positivity) hp₀
          obtain ⟨hlo, hhi⟩ := log_two_bounds (by omega : p₀ ≠ 0)
          rw [hpj] at hlo hhi
          have hlo' : (2 : ℝ) ^ j ≤ p₀ := by exact_mod_cast hlo
          have hhi' : (p₀ : ℝ) < 2 * 2 ^ j := by exact_mod_cast hhi
          have hXj : X ≤ 2 ^ j := by linarith
          have hjX : (2 : ℝ) ^ j ≤ X ^ (1 + δ) := hlo'.trans hp₀3
          have hbc := hcon j hXj hjX
          have hfib : ∀ p ∈ D.filter (fun p => Nat.log 2 p = j),
              Real.log p / (p : ℝ) ^ α ≤ ((j : ℝ) + 1) * Real.log 2 / ((2 : ℝ) ^ j) ^ α := by
            intro p hp
            rw [Finset.mem_filter] at hp
            obtain ⟨-, hp1, -, -⟩ := mem_mertens_sdiff (by positivity) hp.1
            obtain ⟨h1, h2⟩ := log_two_bounds (by omega : p ≠ 0)
            rw [hp.2] at h1 h2
            exact term_le hα.le h1 h2
          have hcard : (D.filter (fun p => Nat.log 2 p = j)).card ≤ blockCount S (2 ^ j) := by
            apply Finset.card_le_card
            intro p hp
            rw [Finset.mem_filter] at hp
            obtain ⟨hpS, hp1, -, -⟩ := mem_mertens_sdiff (by positivity) hp.1
            obtain ⟨h1, h2⟩ := log_two_bounds (by omega : p ≠ 0)
            rw [hp.2] at h1 h2
            simp only [Finset.mem_filter, Finset.mem_Ico]
            exact ⟨⟨h1, h2⟩, hpS⟩
          have hc0 : 0 ≤ ((j : ℝ) + 1) * Real.log 2 / ((2 : ℝ) ^ j) ^ α :=
            div_nonneg (mul_nonneg (by positivity) hl2) (by positivity)
          calc ∑ p ∈ D.filter (fun p => Nat.log 2 p = j), Real.log p / (p : ℝ) ^ α
              ≤ (D.filter (fun p => Nat.log 2 p = j)).card •
                  (((j : ℝ) + 1) * Real.log 2 / ((2 : ℝ) ^ j) ^ α) :=
                Finset.sum_le_card_nsmul _ _ _ hfib
            _ ≤ (blockCount S (2 ^ j) : ℝ) * (((j : ℝ) + 1) * Real.log 2 / ((2 : ℝ) ^ j) ^ α) := by
                rw [nsmul_eq_mul]
                exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hc0
            _ ≤ ((2 : ℝ) ^ j) ^ (α - ε) * (((j : ℝ) + 1) * Real.log 2 / ((2 : ℝ) ^ j) ^ α) :=
                mul_le_mul_of_nonneg_right hbc.le hc0
            _ = Real.log 2 * (((j : ℝ) + 1) * ((2 : ℝ) ^ (-ε)) ^ j) := by
                have hA : 0 < ((2 : ℝ) ^ j) ^ α := by positivity
                have hE : 0 < ((2 : ℝ) ^ j) ^ ε := by positivity
                rw [← two_pow_rpow, Real.rpow_sub (by positivity), Real.rpow_neg (by positivity)]
                field_simp
      _ ≤ T := htsum.sum_le_tsum _ (fun j _ => ht0 j)
  linarith
end DeletedPrimes
