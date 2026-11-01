-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_original_stieltjes_uniform_localisation_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T01:07:49.759782+00:00
-- url     : https://prove2.me/submissions/3eabc89b-f7ea-4b82-a086-7e83d8479727

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_expected_preruin_complete_stieltjes_localisation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A uniform budget for the genuine stopped original-process Stieltjes rewards
passes to the full ruin-stopped reward, including the atom at time zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) (q : ℝ)
    (τ : ℕ → Ω → ℝ≥0∞)
    (hτmeas : ∀ n, Measurable (τ n))
    (hτmono : ∀ ω, Monotone (fun n => τ n ω))
    (hτsup : ∀ ω, (⨆ n, τ n ω) = ruinTime X x D ω)
    (B : ℝ≥0∞)
    (hBound : ∀ n,
      (∫⁻ ω : Ω,
          ∫⁻ s in paymentTimes (τ n ω) ∩ Iic (T : ℝ),
            ENNReal.ofReal (Real.exp (-q * s))
              ∂dividendMeasure D ω ∂P) ≤ B) :
    (∫⁻ ω : Ω,
        ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
          ENNReal.ofReal (Real.exp (-q * s))
            ∂dividendMeasure D ω ∂P) ≤ B := by
  rw [avram_wave4_04b_expected_preruin_complete_stieltjes_localisation
    X x D hD T q τ hτmeas hτmono hτsup]
  exact iSup_le hBound
