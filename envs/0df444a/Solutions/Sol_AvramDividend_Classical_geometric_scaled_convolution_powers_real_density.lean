-- Prove2me | solution 1 for AvramDividend.Classical.geometric_scaled_convolution_powers_real_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T11:28:48.018708+00:00
-- url     : https://prove2.me/submissions/7b5699a2-eef3-474f-aa2d-bd4238a39d4c

import Mathlib.MeasureTheory.Group.Convolution
import Theorems.Thm_AvramDividend_Classical_double_scalar_measure_convolution
import Theorems.Thm_AvramDividend_Classical_nonnegative_real_causal_convolution_powers_density_identification

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Each geometric convolution power has the real density of the rescaled kernel power. -/
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
  let s : ℕ → Measure ℝ := fun n => c ^ (n + 1) • m n
  have hszero : s 0 =
      volume.withDensity (fun x : ℝ => ENNReal.ofReal (k x)) := by
    simpa [s, hmzero] using hκscaled
  have hssucc (n : ℕ) : s (n + 1) =
      (volume.withDensity (fun x : ℝ => ENNReal.ofReal (k x))).conv (s n) := by
    letI : SFinite (m n) := hmsfinite n
    calc
      s (n + 1) = (c * c ^ (n + 1)) • (κ.conv (m n)) := by
        simp [s, hmsucc n, pow_succ, mul_comm, mul_left_comm, mul_assoc]
      _ = (c • κ).conv (c ^ (n + 1) • m n) :=
        (double_scalar_measure_convolution c (c ^ (n + 1)) κ (m n)).symm
      _ = (volume.withDensity (fun x : ℝ => ENNReal.ofReal (k x))).conv (s n) := by
        rw [hκscaled]
  exact nonnegative_real_causal_convolution_powers_density_identification
    k F s hkpos hFpos hkmeas hFmeas hconv hFzero hFsucc hszero hssucc
