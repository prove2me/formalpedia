-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_prepayment_compact_cutoff_HJB
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:07:37.012095+00:00
-- url     : https://prove2.me/submissions/198e84e6-cbe2-47bb-900e-ac36551d3feb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_original_epsilon_drift_compact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (q : ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    let Y : ℝ := Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    (0 < Y ∧ ENNReal.ofReal Y < C) →
      X.σ ^ 2 / 2 * iteratedDeriv 2 w Y +
        (X.c - (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν)) * deriv w Y +
        (∫ z in Iio (-ε), w (Y + z) - w Y ∂X.ν) +
        (∫ z in Ico (-ε) 0,
          SpectrallyNegativeLevy.generatorIntegrand w Y z ∂X.ν) -
        q * w Y ≤ 0 := by
  dsimp only
  intro hy
  obtain ⟨hI, hle⟩ := hw_gen
    (Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)
    hy.1 hy.2
  have hFormula :=
    avram_p4_c_generator_original_epsilon_drift_compact X w
      (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)
      ε hε hε1 hI
  rw [hFormula] at hle
  exact hle
