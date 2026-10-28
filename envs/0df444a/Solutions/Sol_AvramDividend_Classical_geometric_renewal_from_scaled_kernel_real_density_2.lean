-- Prove2me | solution 2 for AvramDividend.Classical.geometric_renewal_from_scaled_kernel_real_density
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:31:49.610394+00:00
-- url     : https://prove2.me/submissions/bdd58c20-7f43-429f-b2e0-1e769863ad16

import Mathlib.MeasureTheory.Group.Convolution
import Theorems.Thm_AvramDividend_Classical_geometric_scaled_convolution_powers_real_density
import Theorems.Thm_AvramDividend_Classical_geometric_renewal_measure_atom_plus_real_density
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
    (hFsummable : ∀ x : ℝ,
      Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else F (n - 1) x))
    (hFzero : F 0 = k)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, k y * F n (x - y) ∂volume)
    (hκscaled : c • κ = volume.withDensity
      (fun x : ℝ => ENNReal.ofReal (k x)))
    (hmzero : m 0 = Measure.dirac (0 : ℝ))
    (hmsucc : ∀ n : ℕ, m (n + 1) = κ.conv (m n))
    (hmsfinite : ∀ n : ℕ, SFinite (m n)) :
    Measure.sum (fun n : ℕ => c ^ (n + 1) • m n) =
      c • (Measure.dirac (0 : ℝ) +
        volume.withDensity (fun x : ℝ =>
          ENNReal.ofReal (∑' n : ℕ,
            if n = 0 then (0 : ℝ) else F (n - 1) x))) := by
  refine AvramDividend.Classical.geometric_renewal_measure_atom_plus_real_density c F m hFpos hFmeas
    hFsummable hmzero ?_
  exact AvramDividend.Classical.geometric_scaled_convolution_powers_real_density c κ k F
    (fun n => m (n + 1)) hkpos hFpos hkmeas hFmeas hconv hFzero hFsucc hκscaled
    (by rw [hmsucc, hmzero, Measure.conv_dirac_zero]) (fun n => hmsucc (n + 1))
    (fun n => hmsfinite (n + 1))
