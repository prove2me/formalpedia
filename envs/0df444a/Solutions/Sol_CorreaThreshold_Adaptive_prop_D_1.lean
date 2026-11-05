-- Prove2me | solution 1 for CorreaThreshold.Adaptive.prop_D_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T20:55:35.506563+00:00
-- url     : https://prove2.me/submissions/91e6d334-b3a5-453c-941e-579589ae61a5

import Mathlib
import Definitions.Def_CorreaThreshold_Adaptive_Setting

open MeasureTheory ProbabilityTheory CorreaThreshold.Adaptive

lemma correa2_exp_le_quad {u : ℝ} (hu0 : u ≤ 0) (hu1 : -1 ≤ u) :
    Real.exp u ≤ 1 + u + u ^ 2 / 2 := by
  have habs : |u| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have h := Real.exp_bound habs (n := 4) (by norm_num)
  have hsum : ∑ i ∈ Finset.range 4, u ^ i / (i.factorial : ℝ) = 1 + u + u ^ 2 / 2 + u ^ 3 / 6 := by
    simp [Finset.sum_range_succ, Nat.factorial] <;> ring
  rw [hsum] at h
  have hau : |u| = -u := abs_of_nonpos hu0
  rw [hau] at h
  have h2 := (abs_le.mp h).2
  norm_num [Nat.factorial] at h2
  have hu3 : u ^ 3 / 6 + (-u) ^ 4 * (5 / 96) ≤ 0 := by
    have : (-u) ^ 4 = u ^ 4 := by ring
    rw [this]
    have h4 : 0 ≤ -u ^ 3 := by nlinarith [sq_nonneg u]
    nlinarith [sq_nonneg u, mul_nonneg h4 (by linarith : (0:ℝ) ≤ 1 + u)]
  nlinarith

/-- The key one-variable inequality: for `u ≤ 0` and `m ≥ 1`,
`e^u ≤ 1 + u + (m u² − u)/(2(m+1))`. -/
lemma correa2_key {u m : ℝ} (hu : u ≤ 0) (hm : 1 ≤ m) :
    Real.exp u ≤ 1 + u + (m * u ^ 2 - u) / (2 * (m + 1)) := by
  have hm1 : (0 : ℝ) < m + 1 := by linarith
  rcases le_total (-1) u with h | h
  · have hq := correa2_exp_le_quad hu h
    have : u ^ 2 / 2 ≤ (m * u ^ 2 - u) / (2 * (m + 1)) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [mul_nonneg (neg_nonneg.mpr hu) (by linarith : (0:ℝ) ≤ 1 + u)]
    linarith
  · have he : Real.exp u ≤ Real.exp (-1) := Real.exp_le_exp.mpr h
    have he1 := Real.exp_neg_one_lt_d9
    have h1 : (u ^ 2 - u) / 4 ≤ (m * u ^ 2 - u) / (2 * (m + 1)) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ m - 1)
        (mul_nonneg (neg_nonneg.mpr hu) (by linarith : (0:ℝ) ≤ -1 - u))]
    have h2 : (7 : ℝ) / 16 ≤ 1 + u + (u ^ 2 - u) / 4 := by nlinarith [sq_nonneg (u + 3 / 2)]
    norm_num at he1
    linarith

theorem solution (β : ℝ) (hβ : 5 / 4 < β) (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : x ∈ Set.Ioc 0 1) :
    ((n : ℝ) - 1) / n * x ^ ((n : ℝ) / ((n : ℝ) - 1)) ≤
      x + x * (Real.log x - 1) / n +
        Real.log x * (x * (Real.log x - 1) - (β - 1)) / (2 * (n : ℝ) ^ 2) := by
  obtain ⟨hx0, hx1⟩ := hx
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set m : ℝ := (n : ℝ) - 1 with hm
  have hm1 : 1 ≤ m := by linarith
  have hnm : (n : ℝ) = m + 1 := by rw [hm]; ring
  set L := Real.log x with hL
  have hL0 : L ≤ 0 := Real.log_nonpos hx0.le hx1
  set u := L / m with hu
  have hu0 : u ≤ 0 := div_nonpos_of_nonpos_of_nonneg hL0 (by linarith)
  have hLu : L = m * u := by rw [hu]; field_simp
  -- `x^{n/(n-1)} = x · e^u`
  have hpow : x ^ ((n : ℝ) / m) = x * Real.exp u := by
    rw [Real.rpow_def_of_pos hx0, ← hL]
    have : L * ((n : ℝ) / m) = L + u := by rw [hu, hnm]; field_simp
    rw [this, Real.exp_add, Real.exp_log hx0]
  rw [hpow]
  have hk := correa2_key hu0 hm1
  -- drop the nonnegative `β` term
  have hβterm : 0 ≤ L * (-(β - 1)) / (2 * (n : ℝ) ^ 2) := by
    apply div_nonneg _ (by positivity)
    nlinarith
  have hmain : (m / n) * (x * Real.exp u) ≤ x + x * (L - 1) / n + L * (x * (L - 1)) / (2 * (n : ℝ) ^ 2) := by
    rw [hnm, hLu]
    have hm0 : (0 : ℝ) < m + 1 := by linarith
    have hxe : x * Real.exp u ≤ x * (1 + u + (m * u ^ 2 - u) / (2 * (m + 1))) :=
      mul_le_mul_of_nonneg_left hk hx0.le
    have e1 : m / (m + 1) * (x * (1 + u + (m * u ^ 2 - u) / (2 * (m + 1)))) =
        x + x * (m * u - 1) / (m + 1) + m * u * (x * (m * u - 1)) / (2 * (m + 1) ^ 2) := by
      field_simp
      ring
    calc m / (m + 1) * (x * Real.exp u)
        ≤ m / (m + 1) * (x * (1 + u + (m * u ^ 2 - u) / (2 * (m + 1)))) :=
          mul_le_mul_of_nonneg_left hxe (by positivity)
      _ = _ := e1
  have hsplit : L * (x * (L - 1) - (β - 1)) / (2 * (n : ℝ) ^ 2) =
      L * (x * (L - 1)) / (2 * (n : ℝ) ^ 2) + L * (-(β - 1)) / (2 * (n : ℝ) ^ 2) := by ring
  rw [hsplit]
  linarith
