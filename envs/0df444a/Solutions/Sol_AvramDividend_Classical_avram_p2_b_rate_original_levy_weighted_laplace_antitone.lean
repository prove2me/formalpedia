-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_original_levy_weighted_laplace_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:04:27.801841+00:00
-- url     : https://prove2.me/submissions/50c4ea91-23e1-4e87-9345-56322498ce4a

import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_levy_weighted_moment_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ρ δ θ : ℝ) (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ) (hθ : 0 ≤ θ) :
    (∫ y in Iio (0 : ℝ),
      Real.exp ((ρ + δ) * y) * (Real.exp (θ * y) - 1) ^ 4 ∂X.ν) ≤
      ∫ y in Iio (0 : ℝ),
        Real.exp (ρ * y) * (Real.exp (θ * y) - 1) ^ 4 ∂X.ν := by
  have hleft :=
    AvramDividend.Classical.avram_p2_b_rate_original_levy_weighted_moment_integrable
      X (ρ + δ) θ (add_nonneg hρ hδ) hθ
  have hright :=
    AvramDividend.Classical.avram_p2_b_rate_original_levy_weighted_moment_integrable
      X ρ θ hρ hθ
  apply integral_mono_ae hleft hright
  filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
  have hδy : δ * y ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hδ (le_of_lt hy)
  have hbase : (ρ + δ) * y ≤ ρ * y := by
    nlinarith
  have he : Real.exp ((ρ + δ) * y) ≤ Real.exp (ρ * y) :=
    Real.exp_le_exp.mpr hbase
  have hw : 0 ≤ (Real.exp (θ * y) - 1) ^ 4 := by positivity
  exact mul_le_mul_of_nonneg_right he hw
