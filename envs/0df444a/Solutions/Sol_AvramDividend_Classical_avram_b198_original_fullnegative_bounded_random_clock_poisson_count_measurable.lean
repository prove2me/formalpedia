-- Prove2me | solution 1 for AvramDividend.Classical.avram_b198_original_fullnegative_bounded_random_clock_poisson_count_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:41:04.97625+00:00
-- url     : https://prove2.me/submissions/ad6cc1b4-bbde-4f92-b3bf-d5c6b84eb604

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jump_phys13_original_random_interval_negative_cutoff_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_b197_negative_cutoff_marked_measure_mass_tendsto_full_negative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual original complete negative-jump Poisson count on a bounded measurable random physical clock interval is a measurable ENNReal random variable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (σ : Ω → ℝ≥0) (hσ : Measurable σ) :
    Measurable (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (σ ω) ×ˢ Iio (0 : ℝ))) := by
  let N : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 (σ ω) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
  have hCut : ∀ n : ℕ, Measurable (N n) := by
    intro n
    exact avram_jump_phys13_original_random_interval_negative_cutoff_count_measurable
      X n (fun _ : Ω => 0) σ measurable_const hσ
  have hConv : ∀ ω, Tendsto (fun n : ℕ => N n ω)
      atTop (𝓝 (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (σ ω) ×ˢ Iio (0 : ℝ)))) := by
    intro ω
    exact avram_b197_negative_cutoff_marked_measure_mass_tendsto_full_negative
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (σ ω)
  exact ENNReal.measurable_of_tendsto hCut (tendsto_pi_nhds.mpr hConv)
