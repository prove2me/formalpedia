-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_original_stopping_family_uniform_terminal_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:25:57.414352+00:00
-- url     : https://prove2.me/submissions/fc858ccc-a854-4d5a-8bf5-e4141c5e7b29

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
    (σ : ℕ → Ω → ℝ≥0) (W : ℕ → Ω → ℝ)
    (hW : ∀ k ω, W k ω =
      if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
      else riskProcess X x D (σ k ω) ω) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k ω, |w (W k ω)| ≤ B := by
  classical
  obtain ⟨B, hB, hBound⟩ :=
    avram_p4_e_localise_finitecap_continuous_payoff_uniform_bound
      w hw_cont C.toReal ENNReal.toReal_nonneg
  refine ⟨B, hB, ?_⟩
  intro k ω
  by_cases hnonneg : 0 ≤ W k ω
  · apply hBound (W k ω) hnonneg
    have hcap :=
      avram_wave8_08_source_piecewise_stopped_terminal_ofReal_le_cap
        X x C D hD hxc (σ k) (W k) (hW k) ω
    simpa only [ENNReal.ofReal_toReal hfinite] using hcap
  · have hneg : W k ω < 0 := lt_of_not_ge hnonneg
    simp [hw_neg (W k ω) hneg, hB]
