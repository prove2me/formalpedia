-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_original_equispaced_negative_grid_quadratic_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T06:52:17.043477+00:00
-- url     : https://prove2.me/submissions/7ea4fb05-71d2-4009-982a-09bda37bae72

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_borel_marked_grid_count_second_moment_upper_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

/-- The actual source equispaced negative-increment count has its Bernoulli-grid
second moment bounded by np+(np)^2, using the original independent increments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (h : ℝ≥0) (n : ℕ) (ε : ℝ) :
    (∫⁻ ω, (∑ i ∈ Finset.range n,
        ({v : Ω | X.X ((↑(i + 1) : ℝ≥0) * h) v -
            X.X ((i : ℝ≥0) * h) v ≤ -ε}).indicator
          (fun _ => (1 : ℝ≥0∞)) ω) ^ 2 ∂P) ≤
      (n : ℝ≥0∞) * P {ω : Ω | X.X h ω ≤ -ε} +
        ((n : ℝ≥0∞) * P {ω : Ω | X.X h ω ≤ -ε}) ^ 2 := by
  classical
  let t : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * h
  have ht : Monotone t := by
    intro i j hij
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast hij) (by positivity)
  have hTime (i : ℕ) : t (i + 1) - t i = h := by
    change (↑(i + 1) : ℝ≥0) * h - (i : ℝ≥0) * h = h
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    exact add_tsub_cancel_left ((i : ℝ≥0) * h) h
  let p : ℝ≥0∞ := P {ω : Ω | X.X h ω ≤ -ε}
  have hCell (i : ℕ) :
      P {ω : Ω | X.X (t (i + 1)) ω - X.X (t i) ω ≤ -ε} = p := by
    have hLaw :=
      (X.stationaryIncrements (t i) (t (i + 1))
        (ht (Nat.le_succ i))).measure_mem_eq (measurableSet_Iic : MeasurableSet (Iic (-ε)))
    simpa only [hTime, Set.preimage, Set.mem_Iic, p] using hLaw
  have hSum :
      (∑ i ∈ Finset.range n,
        P {ω : Ω | X.X (t (i + 1)) ω - X.X (t i) ω ≤ -ε}) =
        (n : ℝ≥0∞) * p := by
    calc
      _ = ∑ i ∈ Finset.range n, p := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hCell i
      _ = (n : ℝ≥0∞) * p := by simp [nsmul_eq_mul]
  have hBase :=
    avram_wave6_01_original_borel_marked_grid_count_second_moment_upper_bound
      X t ht n (Iic (-ε)) measurableSet_Iic
  simpa only [t, p, Set.mem_Iic, hSum] using hBase
