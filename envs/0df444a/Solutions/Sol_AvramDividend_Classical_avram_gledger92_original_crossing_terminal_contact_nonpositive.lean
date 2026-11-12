-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger92_original_crossing_terminal_contact_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:18:51.438204+00:00
-- url     : https://prove2.me/submissions/4684ac57-2a52-48be-a2e9-3e02c3cd89ba

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_gledger45_global_topcap_monotone_zero_negative
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (ω : Ω)
    (a b : ℝ≥0) (hab : a ≤ b)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    w (x + X.X b ω - rightLimit D b ω) ≤
      w (x + X.X b ω - rightLimit D a ω) := by
  have hmono :=
    avram_wave3_03_dividendStrategy_rightLimit_monotone D hD ω hab
  apply avram_gledger45_global_topcap_monotone_zero_negative
    w C hTopCap hw0 hw_cont hw_neg hw_grad
  linarith
