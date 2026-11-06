-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_h_gaussian_original_largejump_integral_eq_source_tsum_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:47:21.282566+00:00
-- url     : https://prove2.me/submissions/f7133fdf-a97a-4eaa-b111-283464fe476b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_largeband_mark_integrable_from_finite_support
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_largeband_integral_eq_source_tsum_of_integrable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The original X large-jump integral equals its exact source jump-time series
on every path and bounded horizon, unconditionally. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) :
    let j : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    let E : Set (ℝ≥0 × ℝ) := Ioc (0 : ℝ≥0) T ×ˢ Iic (-1 : ℝ)
    avram_p4_h_gaussian_intrinsic_large_jump_sum X T ω =
      ∑' u : ℝ≥0, if 0 < u ∧ j u ≠ 0 then
        E.indicator (fun p : ℝ≥0 × ℝ => p.2) (u, j u) else 0 := by
  intro j E
  have hLarge :=
    avram_p4_h_gaussian_original_largeband_mark_integrable_from_finite_support
      X ω T
  exact
    avram_p4_h_gaussian_original_largeband_integral_eq_source_tsum_of_integrable
      X ω T hLarge
