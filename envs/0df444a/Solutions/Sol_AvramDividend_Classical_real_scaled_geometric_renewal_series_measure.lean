-- Prove2me | solution 1 for AvramDividend.Classical.real_scaled_geometric_renewal_series_measure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:38:03.965767+00:00
-- url     : https://prove2.me/submissions/6712c502-85b9-4f8e-80d8-ebc484c8fc8a

import Mathlib.MeasureTheory.Measure.WithDensity
import Theorems.Thm_AvramDividend_Classical_real_nonnegative_scalar_withDensity
import Theorems.Thm_AvramDividend_Classical_geometric_renewal_from_scaled_kernel_real_density
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal
theorem solution
    (r : ℝ) (hr : 0 ≤ r)
    (K : ℝ → ℝ) (hKpos : ∀ x : ℝ, 0 ≤ K x) (hKmeas : Measurable K)
    (F : ℕ → ℝ → ℝ) (m : ℕ → Measure ℝ)
    (hFpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hFmeas : ∀ n : ℕ, Measurable (F n))
    (hconv : ∀ n : ℕ, ∀ x : ℝ,
      Integrable (fun y : ℝ => (r * K y) * F n (x - y)) volume)
    (hFsummable : ∀ x : ℝ,
      Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else F (n - 1) x))
    (hFzero : F 0 = fun x : ℝ => r * K x)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, (r * K y) * F n (x - y) ∂volume)
    (κ : Measure ℝ) [SFinite κ]
    (hκdensity : κ = volume.withDensity
      (fun x : ℝ => ENNReal.ofReal (K x)))
    (hmzero : m 0 = Measure.dirac (0 : ℝ))
    (hmsucc : ∀ n : ℕ, m (n + 1) = κ.conv (m n))
    (hmsfinite : ∀ n : ℕ, SFinite (m n)) :
    Measure.sum (fun n : ℕ => (ENNReal.ofReal r) ^ (n + 1) • m n) =
      ENNReal.ofReal r • (Measure.dirac (0 : ℝ) +
        volume.withDensity (fun x : ℝ =>
          ENNReal.ofReal (∑' n : ℕ,
            if n = 0 then (0 : ℝ) else F (n - 1) x))) :=
  AvramDividend.Classical.geometric_renewal_from_scaled_kernel_real_density (ENNReal.ofReal r) κ
    (fun x => r * K x) F m (fun x => mul_nonneg hr (hKpos x)) hFpos (hKmeas.const_mul r) hFmeas hconv
    hFsummable hFzero hFsucc
    (by rw [hκdensity, AvramDividend.Classical.real_nonnegative_scalar_withDensity r hr K hKmeas])
    hmzero hmsucc hmsfinite
