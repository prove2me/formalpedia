-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_08_source_piecewise_stopped_terminal_ofReal_le_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:54:09.951603+00:00
-- url     : https://prove2.me/submissions/182fedae-d5fa-483c-b0a6-f315b0d474ed

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
import Theorems.Thm_AvramDividend_Classical_admissibleLe_riskProcess_le_cap_all_times
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω) :
    ∀ ω, ENNReal.ofReal (W ω) ≤ C := by
  intro ω
  rw [hW ω]
  split_ifs with h
  · exact capped_postPaymentReserve_ofReal_le_cap
      X x C D hD hxc ω (τ ω)
  · exact admissibleLe_riskProcess_le_cap_all_times
      X x C D hD hxc ω (τ ω)
