-- Prove2me | solution 2 for BB6Baker.pillai_gap
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-23T22:14:11.602237+00:00
-- url     : https://prove2.me/submissions/76677ce8-7bc8-4be3-8ff5-10dac318fb08
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit
import Theorems.Thm_BB6Kit_kit_bound
import Theorems.Thm_BB6Kit_numerics


namespace BB6SkK

theorem four_lt_three_pow (i : ℕ) (h : 5 ≤ i) : 4 * i + 8 ≤ 3 ^ i := by
  induction i, h using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

end BB6SkK

theorem solution (i k c : ℕ) (hi : 2 ^ 60 ≤ i) (hc : 0 < c) (hc4 : c ≤ 4 * i)
    (hk : 3 ^ i ≤ 2 * i * 2 ^ k) :
    (i : ℤ) + 5 < |2 * 3 ^ i - (c : ℤ) * 2 ^ k| := by
  by_contra hcon
  push_neg at hcon
  have hi5 : 5 ≤ i := le_trans (by norm_num) hi
  have h3 := BB6SkK.four_lt_three_pow i hi5
  -- k ≥ 2
  have hk2 : 2 ≤ k := by
    by_contra hlt
    push_neg at hlt
    have h2k : 2 ^ k ≤ 2 := by interval_cases k <;> norm_num
    have h' := Nat.mul_le_mul_left (2 * i) h2k
    generalize 2 * i * 2 ^ k = Z at hk h'
    omega
  obtain ⟨hlo, hhi⟩ := abs_le.mp hcon
  -- k ≤ 2i + 2
  have hkub : k ≤ 2 * i + 2 := by
    have h1 : (c : ℤ) * 2 ^ k ≤ 2 * 3 ^ i + i + 5 := by linarith
    have h2 : (2:ℤ) ^ k ≤ (c : ℤ) * 2 ^ k :=
      le_mul_of_one_le_left (by positivity) (by exact_mod_cast hc)
    have h3z : ((4 * i + 8 : ℕ) : ℤ) ≤ ((3 ^ i : ℕ) : ℤ) := by exact_mod_cast h3
    push_cast at h3z
    have h4 : (3:ℤ) ^ i ≤ 4 ^ i := by exact_mod_cast Nat.pow_le_pow_left (by norm_num : 3 ≤ 4) i
    have h5 : (4:ℤ) ^ i * 4 = 2 ^ (2 * i + 2) := by rw [pow_add, pow_mul]; norm_num
    have h6 : (2:ℤ) ^ k ≤ 2 ^ (2 * i + 2) := by linarith
    have h6N : (2:ℕ) ^ k ≤ 2 ^ (2 * i + 2) := by exact_mod_cast h6
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h6N
  -- real-number setting
  have hX : (0:ℝ) < (c:ℝ) * 2 ^ k := by
    have : (0:ℝ) < c := by exact_mod_cast hc
    positivity
  have hY : (0:ℝ) < 2 * 3 ^ i := by positivity
  have h3pos : (0:ℝ) < 3 ^ i := by positivity
  have hXY : |(c:ℝ) * 2 ^ k - 2 * 3 ^ i| ≤ (i:ℝ) + 5 := by
    have : |((c : ℤ) * 2 ^ k - 2 * 3 ^ i : ℤ)| ≤ (i : ℤ) + 5 := by rw [abs_sub_comm]; exact hcon
    exact_mod_cast this
  have h3R : 4 * (i:ℝ) + 8 ≤ 3 ^ i := by exact_mod_cast h3
  have hi5nn : (0:ℝ) ≤ (i:ℝ) + 5 := by positivity
  have hΛ : ((k:ℝ) - 1) * Real.log 2 - (i:ℝ) * Real.log 3 + Real.log (c:ℝ) =
      Real.log ((c:ℝ) * 2 ^ k) - Real.log (2 * 3 ^ i) := by
    have hc0 : (c:ℝ) ≠ 0 := by exact_mod_cast hc.ne'
    rw [Real.log_mul hc0 (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_pow, Real.log_pow]
    ring
  -- nonvanishing: c·2^k ≠ 2·3^i (4 divides the left side, not the right)
  have hne_nat : c * 2 ^ k ≠ 2 * 3 ^ i := by
    intro heq
    have hodd : 3 ^ i % 2 = 1 := by rw [Nat.pow_mod]; norm_num
    obtain ⟨j, hj⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    rw [hj, pow_add, show c * (2 ^ j * 2 ^ 2) = 4 * (c * 2 ^ j) by ring] at heq
    generalize c * 2 ^ j = Z at heq
    omega
  have hneR : Real.log ((c:ℝ) * 2 ^ k) - Real.log (2 * 3 ^ i) ≠ 0 := by
    intro h0
    have heqlog : Real.log ((c:ℝ) * 2 ^ k) = Real.log (2 * 3 ^ i) := by linarith
    have heqR := Real.log_injOn_pos (Set.mem_Ioi.mpr hX) (Set.mem_Ioi.mpr hY) heqlog
    have : c * 2 ^ k = 2 * 3 ^ i := by exact_mod_cast heqR
    exact hne_nat this
  -- |Λ| ≤ (i+5)/3^i
  have hA1 := (abs_le.mp hXY).1
  have hA2 := (abs_le.mp hXY).2
  have hmin : (3:ℝ) ^ i ≤ (c:ℝ) * 2 ^ k := by linarith
  have hup1 : Real.log ((c:ℝ) * 2 ^ k) - Real.log (2 * 3 ^ i) ≤ ((i:ℝ) + 5) / 3 ^ i := by
    rw [← Real.log_div hX.ne' hY.ne']
    have h1 := Real.log_le_sub_one_of_pos (div_pos hX hY)
    have h2 : (c:ℝ) * 2 ^ k / (2 * 3 ^ i) - 1 ≤ ((i:ℝ) + 5) / 3 ^ i := by
      rw [div_sub_one hY.ne', div_le_div_iff₀ hY h3pos]
      nlinarith [mul_nonneg (sub_nonneg.mpr hA2) h3pos.le, mul_nonneg hi5nn h3pos.le]
    linarith
  have hup2 : Real.log (2 * 3 ^ i) - Real.log ((c:ℝ) * 2 ^ k) ≤ ((i:ℝ) + 5) / 3 ^ i := by
    rw [← Real.log_div hY.ne' hX.ne']
    have h1 := Real.log_le_sub_one_of_pos (div_pos hY hX)
    have hB : 2 * 3 ^ i - (c:ℝ) * 2 ^ k ≤ (i:ℝ) + 5 := by linarith
    have h2 : 2 * 3 ^ i / ((c:ℝ) * 2 ^ k) - 1 ≤ ((i:ℝ) + 5) / 3 ^ i := by
      rw [div_sub_one hX.ne', div_le_div_iff₀ hX h3pos]
      nlinarith [mul_nonneg (sub_nonneg.mpr hB) h3pos.le, mul_nonneg hi5nn (sub_nonneg.mpr hmin)]
    linarith
  have habs : |Real.log ((c:ℝ) * 2 ^ k) - Real.log (2 * 3 ^ i)| ≤ ((i:ℝ) + 5) / 3 ^ i :=
    abs_le.mpr ⟨by linarith, hup1⟩
  have hlog : Real.log |Real.log ((c:ℝ) * 2 ^ k) - Real.log (2 * 3 ^ i)| ≤
      Real.log ((i:ℝ) + 5) - (i:ℝ) * Real.log 3 := by
    calc _ ≤ Real.log (((i:ℝ) + 5) / 3 ^ i) := Real.log_le_log (abs_pos.mpr hneR) habs
      _ = _ := by rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
  have hA := BB6Kit.kit_bound i k c hi hc hc4 hk2 hkub (by rw [hΛ]; exact hneR)
  rw [hΛ] at hA
  have hN := BB6Kit.numerics i hi
  linarith
