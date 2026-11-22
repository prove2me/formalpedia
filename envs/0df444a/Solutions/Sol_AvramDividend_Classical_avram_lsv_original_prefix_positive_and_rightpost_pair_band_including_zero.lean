-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_original_prefix_positive_and_rightpost_pair_band_including_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:27:45.057806+00:00
-- url     : https://prove2.me/submissions/037bdb06-97d6-4df9-9b57-7f9bd4c97819

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (a b : ℝ) (hxb : x ≤ b)
    (hPre : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      riskProcess X x D t ω ∈ Icc a b)
    (hPost : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t < ρ ω →
      x + X.X t ω - rightLimit D t ω ∈ Icc a b) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t < ρ ω →
      riskProcess X x D t ω ∈ Icc a b ∧
      x + X.X t ω - rightLimit D t ω ∈ Icc a b := by
  filter_upwards [hPre,hPost] with ω hp hpost
  intro t ht
  constructor
  · by_cases hz : t = 0
    · subst t
      have hright := dividendStrategy_le_rightLimit D hD ω 0
      have hzeroD : D 0 ω = 0 := hD.1 ω
      have hzeroX : X.X 0 ω = 0 := X.X_zero ω
      have hpost0 := (hpost 0 ht).1
      have hright0 : 0 ≤ rightLimit D 0 ω := by
        simpa [hzeroD] using hright
      have hxa : a ≤ x := by
        have hp0 : a ≤ x - rightLimit D 0 ω := by
          simpa [hzeroX] using hpost0
        linarith
      simpa [riskProcess,hzeroX,hzeroD] using
        (show x ∈ Icc a b from ⟨hxa,hxb⟩)
    · have h0 : (0 : ℝ≥0) ≤ t := bot_le
      exact hp t (lt_of_le_of_ne h0 (Ne.symm hz)) ht
  · exact hpost t ht
