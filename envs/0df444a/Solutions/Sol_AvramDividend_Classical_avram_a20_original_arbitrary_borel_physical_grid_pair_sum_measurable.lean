-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_arbitrary_borel_physical_grid_pair_sum_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:16:13.721213+00:00
-- url     : https://prove2.me/submissions/50e7fc89-bf4b-4a37-9e94-b1f7702b58d3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_intrinsic_marked_rectangle_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (m : ℕ) (s t : Fin m → ℝ≥0)
    (B : Set ℝ) (hB : MeasurableSet B) :
    let N : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ B)
    Measurable (fun ω => ∑ i : Fin m,
      N 0 (s i) ω * N (s i) (t i) ω) := by
  classical
  let N : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc a b ×ˢ B)
  change Measurable (fun ω => ∑ i : Fin m,
    N 0 (s i) ω * N (s i) (t i) ω)
  apply Finset.measurable_sum
  intro i _
  have h0 : Measurable (N 0 (s i)) := by
    simpa only [N] using
      (avram_p2_d_future_intrinsic_marked_rectangle_measurable
        X 0 (s i) B hB)
  have h1 : Measurable (N (s i) (t i)) := by
    simpa only [N] using
      (avram_p2_d_future_intrinsic_marked_rectangle_measurable
        X (s i) (t i) B hB)
  exact h0.mul h1
