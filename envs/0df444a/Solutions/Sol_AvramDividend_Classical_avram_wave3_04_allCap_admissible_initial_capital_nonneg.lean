-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_allCap_admissible_initial_capital_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T22:11:58.959673+00:00
-- url     : https://prove2.me/submissions/2232d8d6-79ce-4196-80fa-e13b0dda0c97

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_initial_state
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Any genuinely capped admissible original dividend strategy begins
with nonnegative initial capital when capital is inside the cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) :
    0 ≤ x := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨ω, _⟩ : (Set.univ : Set Ω).Nonempty :=
    nonempty_of_measure_ne_zero (μ := P) (s := Set.univ) (by simp)
  have hpost := capped_postPaymentReserve_initial_state
    X x C D hD hxc ω
  have hright : D 0 ω ≤ rightLimit D 0 ω :=
    dividendStrategy_le_rightLimit D hD.1.1 ω 0
  have hD0 : D 0 ω = 0 := hD.1.1.1 ω
  rw [hD0] at hright
  have hInit : 0 ≤ x - rightLimit D 0 ω := by
    simpa only [X.X_zero ω, add_zero] using hpost.1
  linarith
