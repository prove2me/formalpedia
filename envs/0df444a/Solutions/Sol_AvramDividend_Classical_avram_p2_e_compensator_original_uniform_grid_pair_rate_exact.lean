-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_original_uniform_grid_pair_rate_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:10:52.409203+00:00
-- url     : https://prove2.me/submissions/9e668cb6-29dc-4ef1-92f1-370d9cb9e130

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_grid_pair_rate_sum_exact
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_uniform_grid_cell_bounds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The exact original marked-count grid expectation specialises to uniform physical cells. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (k n : ℕ) :
    let s : Fin (k + 1) → ℝ≥0 := fun i =>
      (i.val : ℝ≥0) * (T / ((k : ℝ≥0) + 1))
    let t : Fin (k + 1) → ℝ≥0 := fun i =>
      (((i.val + 1 : ℕ) : ℝ≥0) * (T / ((k : ℝ≥0) + 1)))
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ B)
    (∫⁻ ω, ∑ i : Fin (k + 1), N 0 (s i) ω * N (s i) (t i) ω ∂P) =
      ∑ i : Fin (k + 1), ((s i : ℝ≥0∞) * X.ν B) *
        (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν B) := by
  classical
  let s : Fin (k + 1) → ℝ≥0 := fun i =>
    (i.val : ℝ≥0) * (T / ((k : ℝ≥0) + 1))
  let t : Fin (k + 1) → ℝ≥0 := fun i =>
    (((i.val + 1 : ℕ) : ℝ≥0) * (T / ((k : ℝ≥0) + 1)))
  have hst : ∀ i, s i ≤ t i := by
    intro i
    exact (avram_p2_e_compensator_uniform_grid_cell_bounds T k i).1
  exact avram_p2_e_compensator_original_grid_pair_rate_sum_exact
    X (k + 1) s t hst n
