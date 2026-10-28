-- Prove2me | solution 1 for AvramDividend.Classical.quadratic_exponent_gaussian_grid_mgf_limit_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T13:02:02.839959+00:00
-- url     : https://prove2.me/submissions/773ff8c8-1d23-432f-a8f7-09a9df180780

import Mathlib
import Theorems.Thm_AvramDividend_Classical_quadratic_exponent_limit_nat_multiples_ws01f

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

open Filter
open scoped Topology
open AvramDividend.Classical

theorem solution (f : ℝ → ℝ) (a C : ℝ)
    (hf : Tendsto (fun n : ℕ =>
      f ((n : ℝ) + 1) / (((n : ℝ) + 1) ^ 2))
      atTop (nhds a))
    (m k : ℕ) (hm : 0 < m) (hk : 0 < k) :
    Tendsto (fun n : ℕ =>
      Real.exp
        (f ((k : ℝ) * ((n : ℝ) + 1)) /
            (((m : ℝ) * ((n : ℝ) + 1)) ^ 2) -
          (k : ℝ) * C / ((m : ℝ) ^ 2 * ((n : ℝ) + 1))))
      atTop (nhds (Real.exp (a * ((k : ℝ) / (m : ℝ)) ^ 2))) := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hd (n : ℕ) : 0 < (n : ℝ) + 1 := by positivity
  have hψ := quadratic_exponent_limit_nat_multiples_ws01f f a hf k hk
  let ρ : ℝ := ((k : ℝ) / (m : ℝ)) ^ 2
  have hEqψ :
      (fun n : ℕ => ρ *
        (f ((k : ℝ) * ((n : ℝ) + 1)) /
          (((k : ℝ) * ((n : ℝ) + 1)) ^ 2))) =
      (fun n : ℕ =>
        f ((k : ℝ) * ((n : ℝ) + 1)) /
          (((m : ℝ) * ((n : ℝ) + 1)) ^ 2)) := by
    funext n
    dsimp [ρ]
    field_simp [ne_of_gt hmR, ne_of_gt hkR, ne_of_gt (hd n)] <;> ring
  have hscaled := hψ.const_mul ρ
  rw [hEqψ] at hscaled
  have hcomm : ρ * a = a * ρ := mul_comm _ _
  rw [hcomm] at hscaled
  have hD : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
      atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let γ : ℝ := (k : ℝ) * C / (m : ℝ) ^ 2
  have hEqC :
      (fun n : ℕ => γ * ((1 : ℝ) / ((n : ℝ) + 1))) =
      (fun n : ℕ =>
        (k : ℝ) * C / ((m : ℝ) ^ 2 * ((n : ℝ) + 1))) := by
    funext n
    dsimp [γ]
    field_simp [ne_of_gt hmR, ne_of_gt (hd n)] <;> ring
  have hC := hD.const_mul γ
  have hzero : γ * (0 : ℝ) = 0 := by ring
  rw [hzero] at hC
  rw [hEqC] at hC
  have hE := hscaled.sub hC
  have hlim : a * ρ - 0 = a * ρ := sub_zero _
  rw [hlim] at hE
  have hExp := Real.continuous_exp.continuousAt.tendsto.comp hE
  change Tendsto (fun n : ℕ =>
    Real.exp
      (f ((k : ℝ) * ((n : ℝ) + 1)) /
          (((m : ℝ) * ((n : ℝ) + 1)) ^ 2) -
        (k : ℝ) * C / ((m : ℝ) ^ 2 * ((n : ℝ) + 1))))
    atTop (nhds (Real.exp (a * ρ))) at hExp
  simpa only [ρ] using hExp
