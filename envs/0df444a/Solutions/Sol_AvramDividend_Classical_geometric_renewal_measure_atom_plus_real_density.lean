-- Prove2me | solution 1 for AvramDividend.Classical.geometric_renewal_measure_atom_plus_real_density
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:17:42.24402+00:00
-- url     : https://prove2.me/submissions/fb39e916-d428-4231-9ca8-ca6510d3741e

import Mathlib.MeasureTheory.Measure.WithDensity
import Theorems.Thm_AvramDividend_Classical_geometric_measure_sum_extract_constant
import Theorems.Thm_AvramDividend_Classical_renewal_measure_atom_plus_real_density
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal
theorem solution
    (c : ℝ≥0∞) (F : ℕ → ℝ → ℝ) (m : ℕ → Measure ℝ)
    (hFpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hFmeas : ∀ n : ℕ, Measurable (F n))
    (hFsummable : ∀ x : ℝ,
      Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else F (n - 1) x))
    (hmzero : m 0 = Measure.dirac (0 : ℝ))
    (hmpower : ∀ n : ℕ, c ^ (n + 1) • m (n + 1) =
      volume.withDensity (fun x : ℝ => ENNReal.ofReal (F n x))) :
    Measure.sum (fun n : ℕ => c ^ (n + 1) • m n) =
      c • (Measure.dirac (0 : ℝ) +
        volume.withDensity (fun x : ℝ =>
          ENNReal.ofReal (∑' n : ℕ,
            if n = 0 then (0 : ℝ) else F (n - 1) x))) := by
  rw [AvramDividend.Classical.geometric_measure_sum_extract_constant,
    AvramDividend.Classical.renewal_measure_atom_plus_real_density F (fun n => c ^ n • m n) hFpos hFmeas
      hFsummable (by simp [hmzero]) hmpower]
