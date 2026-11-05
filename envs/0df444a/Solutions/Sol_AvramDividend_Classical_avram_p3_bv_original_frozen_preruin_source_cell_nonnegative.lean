-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_frozen_preruin_source_cell_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:16:12.636404+00:00
-- url     : https://prove2.me/submissions/49c802e0-c912-4af8-8794-23728a2fb25a

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_preruin_postpayment_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- Actual admissibility makes every physical frozen-dividend source endpoint
   nonnegative up to the inclusive initial/strict pre-ruin clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (u : ℕ → ℝ≥0) (i : ℕ)
    (hui : u i ≤ u (i + 1))
    (hLive : u (i + 1) = 0 ∨
      (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    0 ≤ x + X.X (u (i + 1)) ω - rightLimit D (u i) ω := by
  have hPost := avram_p4_e_localise_preruin_postpayment_nonnegative
    X x C D hD ω (u (i + 1)) hLive
  have hMon := avram_wave3_03_dividendStrategy_rightLimit_monotone
    D hD.1.1 ω hui
  linarith
