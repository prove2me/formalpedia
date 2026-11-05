-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_original_grid_pair_lintegral_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:53:20.60544+00:00
-- url     : https://prove2.me/submissions/88d45409-d26b-4883-966d-0a20261f3c88

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_grid_pair_sum_le_total

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (m : ℕ) (s t : Fin m → ℝ≥0) (n : ℕ)
    (hst : ∀ i, s i ≤ t i) (htT : ∀ i, t i ≤ T)
    (hdisj : ∀ i j : Fin m, i ≠ j →
      Disjoint (Ioc (s i) (t i)) (Ioc (s j) (t j))) :
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ B)
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    (∫⁻ ω, ∑ i : Fin m, N 0 (s i) ω * N (s i) (t i) ω ∂P) ≤
      ∫⁻ ω, (((F ω ×ˢ F ω).filter
        (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card : ℝ≥0∞) ∂P := by
  exact MeasureTheory.lintegral_mono (fun ω =>
    avram_p2_e_compensator_original_grid_pair_sum_le_total
      X ω T m s t n hst htT hdisj)
