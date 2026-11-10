-- Prove2me | solution 1 for AvramDividend.Classical.avram_gclose16_original_preruin_negative_increment_forces_strict_postpayment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T22:13:36.567491+00:00
-- url     : https://prove2.me/submissions/0061f397-1962-46cd-ba87-e3c62dc9644f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_preruin_postpayment_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- An actual negative original Levy increment while the strategy still
survives forces strictly positive postpayment reserve at the earlier clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t s : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω)
    (hts : ((t + s : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω)
    (hneg : X.X (t + s) ω - X.X t ω < 0) :
    0 < x + X.X t ω - rightLimit D t ω := by
  have hstart : 0 ≤ x + X.X t ω - rightLimit D t ω :=
    avram_p4_e_localise_preruin_postpayment_nonnegative
      X x C D hD ω t (Or.inr ht)
  have hfinish : 0 ≤ x + X.X (t + s) ω - rightLimit D (t + s) ω :=
    avram_p4_e_localise_preruin_postpayment_nonnegative
      X x C D hD ω (t + s) (Or.inr hts)
  have hmono : rightLimit D t ω ≤ rightLimit D (t + s) ω :=
    (avram_wave3_03_dividendStrategy_rightLimit_monotone
      D hD.1.1 ω) (le_add_of_nonneg_right (zero_le))
  linarith
