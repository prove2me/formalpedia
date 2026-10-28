-- Prove2me | solution 1 for FinancialDerivatives.FD06.heatKernel_semigroup
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:13:55.716769+00:00
-- url     : https://prove2.me/submissions/c28ff434-7709-4ed7-b4ec-d03dba5af362

import Mathlib
import Definitions.Def_fd06_heatKernel

open FinancialDerivatives.FD06

theorem solution (s t x : ℝ) (hs : 0 < s) (ht : 0 < t) : (∫ y : ℝ, heatKernel s (x - y) * heatKernel t y) = heatKernel (s + t) x := by
  have e : ∀ y, heatKernel s (x - y) * heatKernel t y =
      (Real.exp (-(x ^ 2) / (4 * (s + t))) / (Real.sqrt (4 * Real.pi * s) * Real.sqrt (4 * Real.pi * t))) *
        Real.exp (-((s + t) / (4 * s * t)) * (y - t / (s + t) * x) ^ 2) := by
    intro y; unfold heatKernel
    rw [div_mul_div_comm, ← Real.exp_add, mul_comm (Real.exp _ / _), mul_div_assoc', ← Real.exp_add]
    congr 2
    field_simp
    ring
  simp_rw [e]
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_sub_right_eq_self (fun y => Real.exp (-((s + t) / (4 * s * t)) * y ^ 2)),
    integral_gaussian]
  unfold heatKernel
  have h1 : Real.pi / ((s + t) / (4 * s * t)) = 4 * Real.pi * s * (4 * Real.pi * t) / (4 * Real.pi * (s + t)) := by
    field_simp
  rw [h1, Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity)]
  have : 0 < Real.sqrt (4 * Real.pi * (s + t)) := by positivity
  have : 0 < Real.sqrt (4 * Real.pi * s) := by positivity
  have : 0 < Real.sqrt (4 * Real.pi * t) := by positivity
  field_simp
  rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]; congr 1; ring
