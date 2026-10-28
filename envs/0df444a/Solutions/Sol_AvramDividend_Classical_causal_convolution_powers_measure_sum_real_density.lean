-- Prove2me | solution 1 for AvramDividend.Classical.causal_convolution_powers_measure_sum_real_density
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:45:45.789802+00:00
-- url     : https://prove2.me/submissions/72844abe-bc32-464a-b6fd-329fe7d1ca0d

import Mathlib.MeasureTheory.Measure.WithDensity
import Theorems.Thm_AvramDividend_Classical_nonnegative_real_causal_convolution_powers_density_identification
import Theorems.Thm_AvramDividend_Classical_countable_real_density_measure_sum_eq_real_tsum
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal
theorem solution
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (m : ℕ → Measure ℝ)
    (hκpos : ∀ x : ℝ, 0 ≤ κ x)
    (hFpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hκmeas : Measurable κ) (hFmeas : ∀ n : ℕ, Measurable (F n))
    (hconv : ∀ n : ℕ, ∀ x : ℝ,
      Integrable (fun y : ℝ => κ y * F n (x - y)) volume)
    (hFsummable : ∀ x : ℝ, Summable (fun n : ℕ => F n x))
    (hFzero : F 0 = κ)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume)
    (hmzero : m 0 = volume.withDensity
      (fun x : ℝ => ENNReal.ofReal (κ x)))
    (hmsucc : ∀ n : ℕ, m (n + 1) =
      (volume.withDensity (fun x : ℝ => ENNReal.ofReal (κ x))).conv (m n)) :
    Measure.sum m =
      volume.withDensity (fun x : ℝ =>
        ENNReal.ofReal (∑' n : ℕ, F n x)) :=
  AvramDividend.Classical.countable_real_density_measure_sum_eq_real_tsum F m hFmeas hFpos hFsummable
    (AvramDividend.Classical.nonnegative_real_causal_convolution_powers_density_identification κ F m
      hκpos hFpos hκmeas hFmeas hconv hFzero hFsucc hmzero hmsucc)
