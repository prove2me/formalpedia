-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_all_cap_generator_residual_le_overshoot
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:49:42.676379+00:00
-- url     : https://prove2.me/submissions/74533f47-a8c0-4d04-be20-5a4e94e08935

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_generatorIntegrable_strictly_above_real_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_generator_above_eq_drift_add_jump
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_all_cap_positive_jump_part_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_ruin_overshoot_integrable_of_levy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Unconditional original compensated-generator residual bound by the
integrable strict ruin-crossing overshoot, at zero or positive optimal cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : (cstar W).toReal < x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      X.generator (vcstar W) x - q * vcstar W x ≤
        X.c + (∫ y in Ioo (-1 : ℝ) (-x),
          max 0 (-vcstar W x - y) ∂X.ν) - q * vcstar W x := by
  let J : ℝ → ℝ := (Ioo (-1 : ℝ) (-x)).indicator
    (fun y : ℝ => max 0 (-vcstar W x - y))
  have hx0 : 0 < x := lt_of_le_of_lt ENNReal.toReal_nonneg hx
  have hdom := vcstar_generatorIntegrable_strictly_above_real_cstar
    X q W hW x hx
  have hint : IntegrableOn
      (fun y : ℝ => SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y)
      (Iio (0 : ℝ)) X.ν := by
    exact hdom
  have hovers : Integrable J X.ν :=
    avram_wave4_05_source_ruin_overshoot_integrable_of_levy X W x hx0
  have hjump :
      (∫ y in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y ∂X.ν) ≤
      ∫ y in Iio (0 : ℝ), J y ∂X.ν := by
    apply setIntegral_mono_on hint hovers.integrableOn measurableSet_Iio
    intro y hy
    have heq := avram_wave4_05_source_all_cap_positive_jump_part_exact
      X hX q hq W hW x hx y hy
    calc
      SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y ≤
          max 0 (SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y) :=
        le_max_right _ _
      _ = J y := by
        rw [heq]
        by_cases hcross : y ∈ Ioo (-1 : ℝ) (-x)
        · simp [J, hcross, Set.indicator_of_mem hcross]
        · simp [J, hcross, Set.indicator_of_notMem hcross]
  have hsub : Ioo (-1 : ℝ) (-x) ⊆ Iio (0 : ℝ) := by
    intro y hy
    exact lt_trans hy.2 (neg_lt_zero.mpr hx0)
  have hinter : Iio (0 : ℝ) ∩ Ioo (-1 : ℝ) (-x) =
      Ioo (-1 : ℝ) (-x) := Set.inter_eq_right.mpr hsub
  have heqJ :
      (∫ y in Iio (0 : ℝ), J y ∂X.ν) =
      ∫ y in Ioo (-1 : ℝ) (-x),
        max 0 (-vcstar W x - y) ∂X.ν := by
    dsimp [J]
    rw [setIntegral_indicator measurableSet_Ioo]
    rw [hinter]
  refine ⟨hdom, ?_⟩
  rw [vcstar_generator_above_eq_drift_add_jump X W x hx, ← heqJ]
  linarith
