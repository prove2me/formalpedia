-- Prove2me | solution 1 for AvramDividend.Classical.levy_compensated_exponential_primitive_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:21:16.222236+00:00
-- url     : https://prove2.me/submissions/64eb711b-70ec-43e3-8173-3de898776a9f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_kernel_bounds
open MeasureTheory Set intervalIntegral AvramDividend.Classical

theorem solution (θ z : ℝ) (hθ : 0 ≤ θ) (hz : 0 ≤ z) :
    0 ≤ (∫ t in (0 : ℝ)..z, 1 - Real.exp (-θ * t)) ∧
    (∫ t in (0 : ℝ)..z, 1 - Real.exp (-θ * t)) ≤ θ * z ^ 2 / 2 ∧
    (∫ t in (0 : ℝ)..z, 1 - Real.exp (-θ * t)) ≤ z := by
  have hF : IntervalIntegrable
      (fun t : ℝ => 1 - Real.exp (-θ * t)) volume 0 z :=
    (by fun_prop : Continuous
      (fun t : ℝ => 1 - Real.exp (-θ * t))).intervalIntegrable 0 z
  have hZ : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 z :=
    intervalIntegrable_const
  have hOne : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 z :=
    intervalIntegrable_const
  have hLin : IntervalIntegrable (fun t : ℝ => θ * t) volume 0 z :=
    (by fun_prop : Continuous (fun t : ℝ => θ * t)).intervalIntegrable 0 z
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) z) :
      0 ≤ 1 - Real.exp (-θ * t) ∧
      1 - Real.exp (-θ * t) ≤ θ * t :=
    levy_compensated_exponential_kernel_bounds θ t hθ ht.1
  have hpos := intervalIntegral.integral_mono_on hz hZ hF
    (fun t ht => (hbound t ht).1)
  have hsmall := intervalIntegral.integral_mono_on hz hF hLin
    (fun t ht => (hbound t ht).2)
  have hlarge := intervalIntegral.integral_mono_on hz hF hOne
    (fun t ht => by
      have he := Real.exp_nonneg (-θ * t)
      linarith)
  refine ⟨?_, ?_, ?_⟩
  · simpa using hpos
  · have hlin_eval : (∫ t in (0 : ℝ)..z, θ * t) = θ * z ^ 2 / 2 := by
      calc
        _ = θ * (∫ t in (0 : ℝ)..z, t) := by
          rw [intervalIntegral.integral_const_mul]
        _ = θ * ((z ^ 2 - (0 : ℝ) ^ 2) / 2) := by
          rw [integral_id]
        _ = θ * z ^ 2 / 2 := by ring
    simpa only [hlin_eval] using hsmall
  · simpa using hlarge
