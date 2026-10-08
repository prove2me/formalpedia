-- Prove2me | solution 1 for Erdos20.rao_bound
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T16:16:26.457989+00:00
-- url     : https://prove2.me/submissions/6df1838a-5737-4075-b730-9a3649994a9d

import Definitions.Def_Erdos20_defs
import Theorems.Thm_Erdos20_bell_chueluecha_warnke_bound
import Mathlib

namespace Erdos20

/-- Any `k` distinct one-element sets form a sunflower (with empty kernel), so
`f 1 k ≤ k`. -/
theorem f_one_le (k : ℕ) : f 1 k ≤ k := by
  apply Nat.sInf_le
  intro α F ⟨hF, hk⟩
  obtain ⟨S, hSF, hS⟩ := Set.exists_subset_card_eq hk
  refine ⟨S, hSF, hS, ∅, ?_⟩
  intro A hA B hB hAB
  obtain ⟨a, rfl⟩ := Set.ncard_eq_one.mp (hF A (hSF hA))
  obtain ⟨b, rfl⟩ := Set.ncard_eq_one.mp (hF B (hSF hB))
  have hab : a ≠ b := fun h => hAB (by rw [h])
  ext x
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
    not_and]
  rintro rfl rfl
  exact hab rfl

end Erdos20

open Erdos20 in
theorem solution :
    ∃ C : ℝ, 1 < C ∧ ∀ n k : ℕ, 0 < n → 2 ≤ k →
      (Erdos20.f n k : ℝ) ≤ (C * k * Real.log ((k : ℝ) * n)) ^ n + 1 := by
  obtain ⟨C, hC, hbound⟩ := bell_chueluecha_warnke_bound
  refine ⟨C, by linarith, ?_⟩
  intro n k hn hk
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  · -- n = 1: f 1 k ≤ k ≤ C k log k.
    have hn1' : n = 1 := by omega
    subst hn1'
    have hf : (f 1 k : ℝ) ≤ k := by exact_mod_cast f_one_le k
    have hlog2 : (1 : ℝ) / 4 ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have hlogk : Real.log 2 ≤ Real.log k := Real.log_le_log (by norm_num) hk2
    have hk0 : (0 : ℝ) ≤ k := by linarith
    have : (k : ℝ) ≤ C * k * Real.log ((k : ℝ) * (1 : ℕ)) := by
      simp only [Nat.cast_one, mul_one]
      have h1 : (1 : ℝ) ≤ C * Real.log k := by nlinarith
      nlinarith
    simp only [pow_one]
    linarith
  · have h := hbound n k hn2 hk
    have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    have hlog : Real.log n ≤ Real.log ((k : ℝ) * n) :=
      Real.log_le_log (by linarith) (by nlinarith)
    have hbase : 0 ≤ C * k * Real.log n := by positivity
    have hmono : (C * k * Real.log n) ^ n ≤ (C * k * Real.log ((k : ℝ) * n)) ^ n := by
      apply pow_le_pow_left₀ hbase
      apply mul_le_mul_of_nonneg_left hlog (by positivity)
    linarith
