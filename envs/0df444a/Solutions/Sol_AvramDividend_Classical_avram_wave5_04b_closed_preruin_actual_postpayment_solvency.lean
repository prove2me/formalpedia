-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_closed_preruin_actual_postpayment_solvency
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:16:10.986202+00:00
-- url     : https://prove2.me/submissions/02a7217c-7741-4e66-bbf8-76e781d04fe4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Genuine postpayment solvency holds throughout every original pre-ruin closed
time window, including time zero and boundary reserve zero/cap contacts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ≥0)
    (hPre : T = 0 ∨ (T : ℝ≥0∞) < ruinTime X x D ω) :
    ∀ s : ℝ, s ∈ Icc (0 : ℝ) (T : ℝ) →
      0 ≤ x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω := by
  intro s hs
  have hs0 : 0 ≤ s := hs.1
  have hsT : s ≤ (T : ℝ) := hs.2
  have hrepr : (s.toNNReal : ℝ) = s := Real.coe_toNNReal s hs0
  have hleReal : (s.toNNReal : ℝ) ≤ (T : ℝ) := by
    simpa only [hrepr] using hsT
  have hle : s.toNNReal ≤ T := by
    exact_mod_cast hleReal
  have hPreS : s.toNNReal = 0 ∨
      (s.toNNReal : ℝ≥0∞) < ruinTime X x D ω := by
    rcases hPre with hTzero | hTlt
    · left
      apply le_antisymm
      · simpa only [hTzero] using hle
      · exact zero_le
    · right
      have hcoe : (s.toNNReal : ℝ≥0∞) ≤ (T : ℝ≥0∞) := by
        exact_mod_cast hle
      exact lt_of_le_of_lt hcoe hTlt
  have hAdmissible : IsAdmissible X x D := hD.1
  have hCover := hAdmissible.2 ω s.toNNReal hPreS
  dsimp [riskProcess] at hCover
  linarith only [hCover]
