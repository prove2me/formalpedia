-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_support_aligned_dyadic_strict_sublevel_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T00:41:51.89373+00:00
-- url     : https://prove2.me/submissions/127d9e82-b940-4162-9eeb-313e5d30a240

import Mathlib
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_nnreal_tendsto
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_time_ge_nnreal
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_index_mem_finite_grid

open AvramDividend.Classical Filter Set Topology
open scoped NNReal ENNReal
theorem solution (f : ℝ≥0 → ℝ)
    (hr : ∀ u, ContinuousWithinAt f (Ici u) u)
    (T : ℝ≥0) (hT : 0 < T) (a : ℝ) :
    (∃ t : ℝ≥0, t ≤ T ∧ f t < a) ↔
      ∃ n : ℕ, ∃ k : ℕ, k ≤ 2 ^ n ∧
        f (((k : ℝ≥0) / (2 : ℝ≥0) ^ n) * T) < a := by
  constructor
  · rintro ⟨s, hsT, hfs⟩
    have hev : ∀ᶠ r in 𝓝[≥] s, f r < a := (hr s).eventually (gt_mem_nhds hfs)
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
    refine ⟨n, k, hkle, hu ?_⟩
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
  · rintro ⟨n, k, hk2, hk⟩
    refine ⟨_, ?_, hk⟩
    have hkle : (k : ℝ≥0) ≤ 2 ^ n := by exact_mod_cast hk2
    calc (k : ℝ≥0) / 2 ^ n * T ≤ 1 * T := by
          apply mul_le_mul_of_nonneg_right _ zero_le
          exact div_le_one_of_le₀ hkle zero_le
      _ = T := one_mul T
