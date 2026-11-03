-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_04_original_BV_countable_grid_survival_terminal_uniform_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:47:34.354454+00:00
-- url     : https://prove2.me/submissions/de1298f6-f211-44b1-ac10-fb653c8c318e

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.OuterMeasure.AE
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_uniform_strict_survival_terminal_ae_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (H : ℝ≥0)
    (u : ℕ → ℝ≥0) (hu : ∀ n, u n ≤ H) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᵐ ω ∂P, ∀ n : ℕ,
        (if (u n : ℝ≥0∞) < ruinTime X x D ω then
          max 0 (Real.exp (-(q * (u n : ℝ))) *
            w (x + X.X (u n) ω - rightLimit D (u n) ω))
        else 0) ≤ K := by
  obtain ⟨K, hK, hBound⟩ :=
    avram_wave8_04_original_BV_uniform_strict_survival_terminal_ae_bound
      X hX hBV q hq w hw_cont x D hD H
  exact ⟨K, hK, MeasureTheory.ae_all_iff.mpr
    (fun n => hBound (u n) (hu n))⟩
