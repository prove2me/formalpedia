-- Prove2me | solution 2 for AvramDividend.Classical.geometric_renewal_measure_atom_plus_real_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T11:17:58.020195+00:00
-- url     : https://prove2.me/submissions/aac859ea-6134-4113-af6e-a91a4635cbce

import Mathlib.MeasureTheory.Measure.WithDensity
import Theorems.Thm_AvramDividend_Classical_geometric_measure_sum_extract_constant
import Theorems.Thm_AvramDividend_Classical_renewal_measure_atom_plus_real_density

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Expose both initial-atom and real-density normalisations of the geometric renewal sum. -/
theorem solution (c : ℝ≥0∞) (F : ℕ → ℝ → ℝ) (m : ℕ → Measure ℝ)
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
  have htail :
      Measure.sum (fun n : ℕ => c ^ n • m n) =
        Measure.dirac (0 : ℝ) +
          volume.withDensity (fun x : ℝ =>
            ENNReal.ofReal (∑' n : ℕ,
              if n = 0 then (0 : ℝ) else F (n - 1) x)) :=
    renewal_measure_atom_plus_real_density
      F (fun n : ℕ => c ^ n • m n) hFpos hFmeas hFsummable
      (by simpa using hmzero)
      (by intro n; simpa using hmpower n)
  rw [geometric_measure_sum_extract_constant c m, htail]
