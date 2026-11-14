-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_BV_any_shrinking_spatial_width_eventual_positive_physical_drift_after_negative_mark_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:48:44.396643+00:00
-- url     : https://prove2.me/submissions/055629e6-be9c-4649-ad21-55e82d11eec5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_any_spatial_boundary_width_truncated_negative_mark_first_moment_vanish
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hd : 0 < X.drift) (q : ℝ)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n ∧ ε n ≤ 1)
    (hεlim : Tendsto ε atTop (𝓝 (0 : ℝ))) :
    ∀ᶠ n : ℕ in atTop,
      q * ε n + (∫ z in Iio (0 : ℝ), min (ε n) (-z) ∂X.ν) <
        X.drift := by
  have hJ :=
    avram_bva_a22_original_BV_any_spatial_boundary_width_truncated_negative_mark_first_moment_vanish
      X hBV ε hε hεlim
  have hQ : Tendsto (fun n => q * ε n) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hεlim
  have hSum : Tendsto
      (fun n => q * ε n +
        (∫ z in Iio (0 : ℝ), min (ε n) (-z) ∂X.ν))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [add_zero] using hQ.add hJ
  exact (tendsto_order.1 hSum).2 X.drift hd
