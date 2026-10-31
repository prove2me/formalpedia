-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_zeroCap_admissibleInitialCapital_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:56:12.639817+00:00
-- url     : https://prove2.me/submissions/4590924c-3240-4b73-b039-72eeaa5be0ef

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

/-- Any genuinely admissible zero-cap strategy with initial capital
within its cap must start with exactly zero initial capital. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ (0 : ℝ≥0∞))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x 0 D) : x = 0 := by
  have hxle : x ≤ 0 := by
    exact ENNReal.ofReal_eq_zero.mp (bot_unique hxc)
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨ω, _⟩ : (Set.univ : Set Ω).Nonempty :=
    nonempty_of_measure_ne_zero (μ := P) (s := Set.univ) (by simp)
  have hpost := capped_postPaymentReserve_initial_state
    X x 0 D hD hxc ω
  have hright : D 0 ω ≤ rightLimit D 0 ω :=
    dividendStrategy_le_rightLimit D hD.1.1 ω 0
  have hD0 : D 0 ω = 0 := hD.1.1.1 ω
  have hxge : 0 ≤ x := by
    rw [hD0] at hright
    have hInit : 0 ≤ x - rightLimit D 0 ω := by
      simpa only [X.X_zero ω, add_zero] using hpost.1
    linarith
  exact le_antisymm hxle hxge
