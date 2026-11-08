-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_original_piecewise_terminal_w_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:01:48.070208+00:00
-- url     : https://prove2.me/submissions/cdad7436-bbca-4e30-865d-558b7b1dc18b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_08_source_piecewise_stopped_terminal_ofReal_le_cap
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_finitecap_continuous_payoff_uniform_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hfinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (σ ω) ω - rightLimit D (σ ω) ω
      else riskProcess X x D (σ ω) ω) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ω, |w (W ω)| ≤ B := by
  classical
  obtain ⟨B, hB, hBound⟩ :=
    avram_p4_e_localise_finitecap_continuous_payoff_uniform_bound
      w hw_cont C.toReal ENNReal.toReal_nonneg
  refine ⟨B, hB, ?_⟩
  intro ω
  by_cases hnonneg : 0 ≤ W ω
  · apply hBound (W ω) hnonneg
    have hcap :=
      avram_wave8_08_source_piecewise_stopped_terminal_ofReal_le_cap
        X x C D hD hxc σ W hW ω
    simpa only [ENNReal.ofReal_toReal hfinite] using hcap
  · have hneg : W ω < 0 := lt_of_not_ge hnonneg
    simp [hw_neg (W ω) hneg, hB]
