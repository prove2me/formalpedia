-- Prove2me | solution 2 for AvramDividend.Classical.geometric_scaled_convolution_powers_real_density
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:29:01.73708+00:00
-- url     : https://prove2.me/submissions/5d81924b-5806-4b3e-b483-4bcf3084571d

import Mathlib.MeasureTheory.Group.Convolution
import Theorems.Thm_AvramDividend_Classical_double_scalar_measure_convolution
import Theorems.Thm_AvramDividend_Classical_nonnegative_real_causal_convolution_powers_density_identification
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal
theorem solution
    (c : ℝ≥0∞) (κ : Measure ℝ) [SFinite κ]
    (k : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (m : ℕ → Measure ℝ)
    (hkpos : ∀ x : ℝ, 0 ≤ k x)
    (hFpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hkmeas : Measurable k) (hFmeas : ∀ n : ℕ, Measurable (F n))
    (hconv : ∀ n : ℕ, ∀ x : ℝ,
      Integrable (fun y : ℝ => k y * F n (x - y)) volume)
    (hFzero : F 0 = k)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, k y * F n (x - y) ∂volume)
    (hκscaled : c • κ = volume.withDensity
      (fun x : ℝ => ENNReal.ofReal (k x)))
    (hmzero : m 0 = κ)
    (hmsucc : ∀ n : ℕ, m (n + 1) = κ.conv (m n))
    (hmsfinite : ∀ n : ℕ, SFinite (m n)) :
    ∀ n : ℕ, c ^ (n + 1) • m n =
      volume.withDensity (fun x : ℝ => ENNReal.ofReal (F n x)) := by
  refine AvramDividend.Classical.nonnegative_real_causal_convolution_powers_density_identification k F
    (fun n => c ^ (n + 1) • m n) hkpos hFpos hkmeas hFmeas hconv hFzero hFsucc ?_ ?_
  · simp only [zero_add, pow_one, hmzero, hκscaled]
  · intro n
    show c ^ (n + 1 + 1) • m (n + 1) = _
    rw [← hκscaled, AvramDividend.Classical.double_scalar_measure_convolution, hmsucc, ← pow_succ']
