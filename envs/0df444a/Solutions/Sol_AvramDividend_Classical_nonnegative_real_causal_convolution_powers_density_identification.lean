-- Prove2me | solution 1 for AvramDividend.Classical.nonnegative_real_causal_convolution_powers_density_identification
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:27:02.951283+00:00
-- url     : https://prove2.me/submissions/7f0a8d0d-f146-4ac3-a1da-d5f80c221586

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_nonnegative_real_convolution_lconvolution_ofReal_bridge
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal
theorem solution
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (m : ℕ → Measure ℝ)
    (hκpos : ∀ x : ℝ, 0 ≤ κ x)
    (hFpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hκmeas : Measurable κ) (hFmeas : ∀ n : ℕ, Measurable (F n))
    (hconv : ∀ n : ℕ, ∀ x : ℝ,
      Integrable (fun y : ℝ => κ y * F n (x - y)) volume)
    (hFzero : F 0 = κ)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume)
    (hmzero : m 0 = volume.withDensity
      (fun x : ℝ => ENNReal.ofReal (κ x)))
    (hmsucc : ∀ n : ℕ, m (n + 1) =
      (volume.withDensity (fun x : ℝ => ENNReal.ofReal (κ x))).conv (m n)) :
    ∀ n : ℕ, m n = volume.withDensity
      (fun x : ℝ => ENNReal.ofReal (F n x)) := by
  intro n
  induction n with
  | zero => rw [hmzero, hFzero]
  | succ n ih =>
    rw [hmsucc, ih, conv_withDensity_eq_lconvolution hκmeas.ennreal_ofReal
      (hFmeas n).ennreal_ofReal, hFsucc]
    congr 1
    funext x
    exact AvramDividend.Classical.nonnegative_real_convolution_lconvolution_ofReal_bridge
      κ (F n) x hκpos (hFpos n) (hconv n x)
