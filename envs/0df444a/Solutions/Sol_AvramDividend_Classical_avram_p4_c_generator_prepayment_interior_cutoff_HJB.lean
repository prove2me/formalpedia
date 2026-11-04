-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_prepayment_interior_cutoff_HJB
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:06:50.937936+00:00
-- url     : https://prove2.me/submissions/f41dd441-6734-4473-b6bd-8346aedbe391

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_negative_mark_integral_cutoff_split

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
    (ε : ℝ) (hε : 0 < ε) :
    let Y : ℝ := Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    (0 < Y ∧ ENNReal.ofReal Y < C) →
      X.GeneratorIntegrable w Y ∧
      (X.σ ^ 2 / 2 * iteratedDeriv 2 w Y + X.c * deriv w Y +
        (∫ z in Iio (-ε), SpectrallyNegativeLevy.generatorIntegrand w Y z ∂X.ν) +
        (∫ z in Ico (-ε) 0, SpectrallyNegativeLevy.generatorIntegrand w Y z ∂X.ν) -
        q * w Y ≤ 0) := by
  dsimp only
  intro hy
  obtain ⟨hI, hle⟩ := hw_gen
    (Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)
    hy.1 hy.2
  refine ⟨hI, ?_⟩
  have hsplit := avram_p4_c_generator_negative_mark_integral_cutoff_split X w
    (Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)
    ε hε hI
  change X.σ ^ 2 / 2 *
      iteratedDeriv 2 w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) +
      X.c * deriv w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) +
      (∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand w
          (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) z ∂X.ν) -
      q * w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ≤ 0 at hle
  rw [hsplit] at hle
  convert hle using 1 <;> ring
