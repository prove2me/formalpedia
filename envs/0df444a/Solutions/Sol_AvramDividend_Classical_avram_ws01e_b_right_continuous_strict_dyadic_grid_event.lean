-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_right_continuous_strict_dyadic_grid_event
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T00:39:23.61275+00:00
-- url     : https://prove2.me/submissions/96ec7fde-63f5-4036-8bb2-1379cfdcb976

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_scaled_dyadic_ceiling_horizon_limit
open Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    (f : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (hcont : ∀ s : ℝ≥0, ContinuousWithinAt f (Set.Ici s) s)
    (a : ℝ) :
    (∃ s : ℝ≥0, s ≤ T ∧ f s < a) ↔
    (∃ n : ℕ, ∃ k : Fin ((2 : ℕ) ^ n + 1),
      f (((k.val : ℝ≥0) / (2 : ℝ≥0) ^ n) * T) < a) := by
  constructor
  · rintro ⟨s, hsT, hfs⟩
    have hev : ∀ᶠ r in 𝓝[≥] s, f r < a := (hcont s).eventually (gt_mem_nhds hfs)
    obtain ⟨u, hsu, hu⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hev
    have hδ : 0 < u - s := tsub_pos_of_lt hsu
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (T / (u - s)) (by norm_num : (1 : ℝ≥0) < 2)
    have h2n : (0 : ℝ≥0) < 2 ^ n := by positivity
    set k : ℕ := ⌈s * 2 ^ n / T⌉₊ with hk
    have hkle : k ≤ 2 ^ n := by
      apply Nat.ceil_le.mpr
      rw [div_le_iff₀ hT]
      push_cast
      calc s * 2 ^ n ≤ T * 2 ^ n := mul_le_mul_of_nonneg_right hsT (by positivity)
        _ = 2 ^ n * T := mul_comm _ _
    refine ⟨n, ⟨k, Nat.lt_succ_of_le hkle⟩, hu ?_⟩
    simp only
    have hk1 : s * 2 ^ n / T ≤ (k : ℝ≥0) := Nat.le_ceil _
    have hk2 : (k : ℝ≥0) < s * 2 ^ n / T + 1 := Nat.ceil_lt_add_one zero_le
    constructor
    · -- s ≤ k / 2^n * T
      rw [div_le_iff₀ hT] at hk1
      rw [div_mul_eq_mul_div, le_div_iff₀ h2n]
      calc s * 2 ^ n = s * 2 ^ n / T * T := by rw [div_mul_cancel₀ _ hT.ne']
        _ ≤ (k : ℝ≥0) * T := by rw [div_mul_cancel₀ _ hT.ne']; exact hk1
    · -- k / 2^n * T < u
      have hTn : T / 2 ^ n < u - s := by
        rw [div_lt_iff₀ h2n]
        rw [div_lt_iff₀ hδ] at hn
        calc T < 2 ^ n * (u - s) := hn
          _ = (u - s) * 2 ^ n := mul_comm _ _
      have : (k : ℝ≥0) / 2 ^ n * T < s + T / 2 ^ n := by
        calc (k : ℝ≥0) / 2 ^ n * T < (s * 2 ^ n / T + 1) / 2 ^ n * T := by
              apply mul_lt_mul_of_pos_right _ hT
              exact div_lt_div_of_pos_right hk2 h2n
          _ = s + T / 2 ^ n := by field_simp
      calc (k : ℝ≥0) / 2 ^ n * T < s + T / 2 ^ n := this
        _ ≤ s + (u - s) := by gcongr
        _ = u := add_tsub_cancel_of_le hsu.le
  · rintro ⟨n, k, hk⟩
    refine ⟨_, ?_, hk⟩
    have hkle : (k.val : ℝ≥0) ≤ 2 ^ n := by exact_mod_cast Nat.lt_succ_iff.mp k.isLt
    calc (k.val : ℝ≥0) / 2 ^ n * T ≤ 1 * T := by
          apply mul_le_mul_of_nonneg_right _ zero_le
          exact div_le_one_of_le₀ hkle zero_le
      _ = T := one_mul T
