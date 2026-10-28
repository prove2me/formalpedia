-- Prove2me | solution 1 for AvramDividend.Classical.geometric_renewal_from_scaled_kernel_real_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T11:31:24.970074+00:00
-- url     : https://prove2.me/submissions/33176ad4-b8dc-4e9a-8d86-9124bc423287

import Mathlib.MeasureTheory.Group.Convolution
import Theorems.Thm_AvramDividend_Classical_geometric_scaled_convolution_powers_real_density
import Theorems.Thm_AvramDividend_Classical_geometric_renewal_measure_atom_plus_real_density

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Geometric renewal from the real density of the scaled convolution kernel. -/
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
  have hmone : m 1 = κ := by
    simpa [hmzero] using hmsucc 0
  have hpositive :
      ∀ n : ℕ, c ^ (n + 1) • m (n + 1) =
        volume.withDensity (fun x : ℝ => ENNReal.ofReal (F n x)) :=
    geometric_scaled_convolution_powers_real_density
      c κ k F (fun n => m (n + 1))
      hkpos hFpos hkmeas hFmeas hconv hFzero hFsucc hκscaled
      (by simpa using hmone)
      (by intro n; simpa [Nat.add_assoc] using hmsucc (n + 1))
      (by intro n; exact hmsfinite (n + 1))
  exact geometric_renewal_measure_atom_plus_real_density
    c F m hFpos hFmeas hFsummable hmzero hpositive
