-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_ennreal_finite_cap_stopped_terminal_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:20:53.025291+00:00
-- url     : https://prove2.me/submissions/1d169ecd-342f-438a-96f8-50e9b6ecefde

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_finite_cap_stopped_terminal_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact canonical ENNReal cap has terminal L1 whenever finite:
    convert its admissible bound to the real-cap source helper. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hCfin : C ≠ ⊤)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P) :
    Integrable Term P := by
  have hCeq : ENNReal.ofReal C.toReal = C :=
    ENNReal.ofReal_toReal hCfin
  have hDreal : IsAdmissibleLe X x (ENNReal.ofReal C.toReal) D := by
    simpa only [hCeq] using hD
  have hxreal : ENNReal.ofReal x ≤ ENNReal.ofReal C.toReal := by
    simpa only [hCeq] using hxc
  exact
    avram_p4_f_assembly_original_finite_cap_stopped_terminal_integrable
      X q hq w C.toReal ENNReal.toReal_nonneg hw_cont hw_neg
      x hxreal D hDreal τ W Term hW hTerm hTermMeas
