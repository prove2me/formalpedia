-- Prove2me | solution 1 for AvramDividend.Classical.positiveLaplace_geometric_measure_sum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T04:07:46.768302+00:00
-- url     : https://prove2.me/submissions/e2f31ff3-4a25-43fa-bfa4-9015fb455ed2

import Mathlib

open MeasureTheory Set NNReal ENNReal in
theorem solution (m : ℕ → Measure ℝ) (θ : ℝ) (a c : ℝ≥0∞)
    (hm : ∀ n : ℕ,
      (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-θ * x)) ∂m n) = a ^ n) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-θ * x)) ∂
       Measure.sum (fun n : ℕ => c ^ (n + 1) • m n)) =
      c * (1 - c * a)⁻¹ := by
  rw [lintegral_sum_measure]
  have h : ∀ n : ℕ, (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-θ * x)) ∂(c ^ (n + 1) • m n))
      = c * (c * a) ^ n := by
    intro n
    rw [lintegral_smul_measure, hm]
    try simp only [smul_eq_mul]
    rw [_root_.pow_succ, _root_.mul_pow]
    ring
  simp_rw [h]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
