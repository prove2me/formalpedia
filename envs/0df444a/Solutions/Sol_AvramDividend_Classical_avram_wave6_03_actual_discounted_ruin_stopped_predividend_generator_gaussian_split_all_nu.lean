-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_actual_discounted_ruin_stopped_predividend_generator_gaussian_split_all_nu
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:57:34.833308+00:00
-- url     : https://prove2.me/submissions/2008bb5f-e702-449c-a973-2750aa3a5f67

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_original_discounted_gaussian_generator_split_export

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T t : ℝ≥0) (ω : Ω) :
    let y : ℝ := Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let k : ℝ := if t ≤ T then
      (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then 1 else 0) else 0
    k * (Real.exp (-(q * (t : ℝ))) * (X.generator w y - q * w y)) =
      k * (Real.exp (-(q * (t : ℝ))) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w y)) +
      k * (Real.exp (-(q * (t : ℝ))) *
        (X.c * deriv w y +
          (∫ z in Iio (0 : ℝ),
            SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) -
              q * w y)) := by
  dsimp only
  rw [avram_wave5_03a_original_discounted_gaussian_generator_split_export
    X w q (t : ℝ)
    (Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)]
  ring
