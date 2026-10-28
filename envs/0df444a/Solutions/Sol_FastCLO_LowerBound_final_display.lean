-- Prove2me | solution 1 for FastCLO.LowerBound.final_display
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:54:27.205999+00:00
-- url     : https://prove2.me/submissions/69e9d1e0-2b97-42b4-bf79-9a2ffa7c2538

import Mathlib

theorem solution (α : ℝ) (hα : 0 ≤ α) (η n : ℕ) (hη : 2 ≤ η)
    (hn : (2 : ℝ) ^ (2 + α) * ((η : ℝ) - 1) ≤ n) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    let ζ : ℝ := (((η : ℝ) - 1) / n) ^ (1 / (2 + α))
    ρ / (2 * Real.exp 4) * (((η : ℝ) - 1) / n) ^ ((1 + α) / (2 + α)) ≤
      ζ ^ (α + 1) * ρ / 2 * Real.exp (-(2 * ζ / (1 - ζ)) * Real.sqrt (n * ζ ^ α / ((η : ℝ) - 1))) := by
  intro ζ
  have hζdef : ζ = (((η : ℝ) - 1) / n) ^ (1 / (2 + α)) := rfl
  have hη1 : (1 : ℝ) ≤ (η : ℝ) - 1 := by
    have : (2 : ℝ) ≤ η := by exact_mod_cast hη
    linarith
  have h2a : 0 < (2 : ℝ) + α := by linarith
  have hpow2 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 + α) := Real.one_le_rpow (by norm_num) h2a.le
  have hnpos : (0 : ℝ) < n := by nlinarith
  set x := ((η : ℝ) - 1) / n with hxdef
  have hx0 : 0 < x := div_pos (by linarith) hnpos
  have hζpos : 0 < ζ := Real.rpow_pos_of_pos hx0 _
  have hζx : ζ ^ (2 + α) = x := by
    rw [hζdef, ← Real.rpow_mul hx0.le, one_div, inv_mul_cancel₀ h2a.ne', Real.rpow_one]
  have hxle : x ≤ (1 / 2 : ℝ) ^ (2 + α) := by
    rw [Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow, hxdef,
      div_le_div_iff₀ hnpos (by positivity)]
    linarith
  have hζhalf : ζ ≤ 1 / 2 := by
    rw [← Real.rpow_le_rpow_iff hζpos.le (by norm_num) h2a, hζx]
    exact hxle
  have hA : ζ ^ (α + 1) = x ^ ((1 + α) / (2 + α)) := by
    rw [hζdef, ← Real.rpow_mul hx0.le]
    congr 1
    field_simp
    ring
  have hx2 : ζ ^ α * ζ ^ 2 = x := by
    rw [← hζx, add_comm, Real.rpow_add hζpos, Real.rpow_two]
  have hne : ((η : ℝ) - 1) ≠ 0 := by linarith
  have hsq : (n : ℝ) * ζ ^ α / ((η : ℝ) - 1) = (1 / ζ) ^ 2 := by
    have h3 : ζ ^ α * ζ ^ 2 * n = (η : ℝ) - 1 := by rw [hx2, hxdef]; field_simp
    rw [div_eq_iff hne, ← h3]
    field_simp
  have hB : Real.sqrt ((n : ℝ) * ζ ^ α / ((η : ℝ) - 1)) = 1 / ζ := by
    rw [hsq, Real.sqrt_sq (by positivity)]
  have h1z : 0 < 1 - ζ := by linarith
  have hC : -(2 * ζ / (1 - ζ)) * (1 / ζ) = -2 / (1 - ζ) := by
    field_simp
  rw [hA, hB, hC]
  have hE : Real.exp (-4) ≤ Real.exp (-2 / (1 - ζ)) := by
    apply Real.exp_le_exp.2
    rw [le_div_iff₀ h1z]
    linarith
  have hX : 0 ≤ x ^ ((1 + α) / (2 + α)) := Real.rpow_nonneg hx0.le _
  have hL : ρ / (2 * Real.exp 4) * x ^ ((1 + α) / (2 + α)) =
      x ^ ((1 + α) / (2 + α)) * ρ / 2 * Real.exp (-4) := by
    rw [Real.exp_neg]; field_simp
  rw [hL]
  exact mul_le_mul_of_nonneg_left hE (by positivity)
