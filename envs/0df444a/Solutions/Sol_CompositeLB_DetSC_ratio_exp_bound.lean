-- Prove2me | solution 1 for CompositeLB.DetSC.ratio_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:40:30.211077+00:00
-- url     : https://prove2.me/submissions/6ddb2c17-bb3c-4f6c-9ca1-3ab046f0b102

import Mathlib
set_option autoImplicit false

theorem solution (Q q : ℝ) (hQ : 1 < Q)
    (hq : q = (Real.sqrt Q - 1) / (Real.sqrt Q + 1))
    (t k : ℕ)
    (hk : (k : ℤ) + 1 = ⌈(t : ℝ) - 1 / (2 * Real.log q)⌉) :
    (q ^ (2 * t) - q ^ (2 * k + 2)) / Real.sqrt Q ≥
        q ^ (2 * t) / (2 * Real.sqrt Q) ∧
      q ^ (2 * t) / (2 * Real.sqrt Q) ≥
        1 / (2 * Real.sqrt Q) *
          Real.exp (-4 * (t : ℝ) / (Real.sqrt Q - 1)) := by
  set s := Real.sqrt Q with hs
  have hs1 : 1 < s := by
    rw [hs]
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ < Real.sqrt Q := Real.sqrt_lt_sqrt (by norm_num) hQ
  have hs0 : 0 < s := by linarith
  have hq0 : 0 < q := by
    rw [hq]; apply div_pos <;> linarith
  have hq1 : q < 1 := by
    rw [hq, div_lt_one (by linarith)]; linarith
  set L := Real.log q with hL
  have hLneg : L < 0 := Real.log_neg hq0 hq1
  have hpow : ∀ n : ℕ, q ^ n = Real.exp (n * L) := by
    intro n
    rw [Real.exp_nat_mul, hL, Real.exp_log hq0]
  have hceil : (t : ℝ) - 1 / (2 * L) ≤ (k : ℝ) + 1 := by
    have h1 := Int.le_ceil ((t : ℝ) - 1 / (2 * L))
    rw [← hk] at h1
    simpa using h1
  have hL0 : L ≠ 0 := hLneg.ne
  have hLge : -2 / (s - 1) ≤ L := by
    have h := Real.one_sub_inv_le_log_of_pos hq0
    have h2 : 1 - q⁻¹ = -2 / (s - 1) := by
      rw [hq]
      have : s - 1 ≠ 0 := by linarith
      have : s + 1 ≠ 0 := by linarith
      field_simp
      ring
    linarith
  have hexp1 : Real.exp (-1) ≤ 1 / 2 := by
    have h1 := Real.exp_one_gt_d9
    have h2 : Real.exp (-1) * Real.exp 1 = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-1)]
  constructor
  · have h1 : q ^ (2 * k + 2) ≤ q ^ (2 * t) / 2 := by
      rw [hpow, hpow]
      have h2 : ((2 * k + 2 : ℕ) : ℝ) * L ≤ ((2 * t : ℕ) : ℝ) * L + (-1) := by
        push_cast
        have h3 : (2 * (t : ℝ) - 1 / L) ≤ 2 * (k : ℝ) + 2 := by
          have : 1 / (2 * L) = (1 / L) / 2 := by field_simp
          rw [this] at hceil
          linarith
        have h4 : (2 * (t : ℝ) - 1 / L) * L ≥ (2 * (k : ℝ) + 2) * L :=
          mul_le_mul_of_nonpos_right h3 hLneg.le
        have h5 : (2 * (t : ℝ) - 1 / L) * L = 2 * t * L - 1 := by
          field_simp
        linarith
      calc Real.exp (((2 * k + 2 : ℕ) : ℝ) * L)
          ≤ Real.exp (((2 * t : ℕ) : ℝ) * L + (-1)) := Real.exp_le_exp.mpr h2
        _ = Real.exp (((2 * t : ℕ) : ℝ) * L) * Real.exp (-1) := Real.exp_add _ _
        _ ≤ Real.exp (((2 * t : ℕ) : ℝ) * L) * (1 / 2) :=
            mul_le_mul_of_nonneg_left hexp1 (Real.exp_pos _).le
        _ = Real.exp (((2 * t : ℕ) : ℝ) * L) / 2 := by ring
    have h6 : q ^ (2 * t) / (2 * s) ≤ (q ^ (2 * t) - q ^ (2 * k + 2)) / s := by
      have h7 : (q ^ (2 * t) - q ^ (2 * k + 2)) / s - q ^ (2 * t) / (2 * s)
          = (q ^ (2 * t) / 2 - q ^ (2 * k + 2)) / s := by
        field_simp
        ring
      have h8 : 0 ≤ (q ^ (2 * t) / 2 - q ^ (2 * k + 2)) / s :=
        div_nonneg (by linarith) hs0.le
      linarith
    exact h6
  · have h1 : Real.exp (-4 * (t : ℝ) / (s - 1)) ≤ q ^ (2 * t) := by
      rw [hpow]
      apply Real.exp_le_exp.mpr
      have h2 : -4 * (t : ℝ) / (s - 1) = 2 * t * (-2 / (s - 1)) := by
        field_simp
        ring
      rw [h2]
      push_cast
      have ht : (0 : ℝ) ≤ 2 * t := by positivity
      nlinarith
    have h3 : 1 / (2 * s) * Real.exp (-4 * (t : ℝ) / (s - 1)) ≤ 1 / (2 * s) * q ^ (2 * t) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h4 : 1 / (2 * s) * q ^ (2 * t) = q ^ (2 * t) / (2 * s) := by ring
    linarith
