-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_annulus16_original_zero_origin_centered_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T23:03:48.751599+00:00
-- url     : https://prove2.me/submissions/3aae43a9-1e7b-49fb-aa0c-99e90b2934b7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_annulus15_original_bounded_predictable_annulus_grid_L2_zero_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    (∫ ω, (N ω).toReal - r ∂P) = 0 := by
  dsimp only
  let grid : ℕ → ℝ≥0 := fun i => if i = 0 then 0 else T
  have hGrid : ∀ i, grid i ≤ grid (i + 1) := by
    intro i
    cases i with
    | zero => simp [grid]
    | succ j => simp [grid]
  let H : ℕ → Ω → ℝ := fun _ _ => 1
  have hH : ∀ i,
      StronglyMeasurable[𝓕.rightCont (grid i)] (H i) := by
    intro i
    exact stronglyMeasurable_const
  have hBound : ∀ i ω, |H i ω| ≤ (1 : ℝ) := by
    intro i ω
    simp [H]
  have hcore :=
    (avram_mix_annulus15_original_bounded_predictable_annulus_grid_L2_zero_mean
      X n m hnm grid hGrid H hH 1 hBound 1).2
  simpa [grid, H] using hcore
