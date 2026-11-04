-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_zero_reserve_active_right_atom_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:12:13.15611+00:00
-- url     : https://prove2.me/submissions/842f8070-f852-4f07-8eab-2de7a1c4e271

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Zero prepayment reserve forces zero original right-payment atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (hactive : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω)
    (hzero : riskProcess X x D t ω = 0) :
    dividendMeasure D ω {(t : ℝ)} = 0 := by
  have hmono : D t ω ≤ rightLimit D t ω :=
    dividendStrategy_le_rightLimit D hD.1.1 ω t
  have hbound := hD.1.2 ω t hactive
  rw [hzero] at hbound
  have hdelta : rightLimit D t ω - D t ω = 0 := by
    have hnonneg : 0 ≤ rightLimit D t ω - D t ω := sub_nonneg.mpr hmono
    exact le_antisymm hbound hnonneg
  rw [dividendMeasure_singleton_eq_rightLimit_sub D hD.1.1 ω t, hdelta]
  simp
