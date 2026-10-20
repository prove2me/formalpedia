-- Prove2me | solution 1 for AvramDividend.Classical.admissibleLe_transport_to_rightCont
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T19:22:58.637176+00:00
-- url     : https://prove2.me/submissions/0191fcbf-cb59-478a-b4e6-3f9c1b88d6d2

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightCont_filtration
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : SpectrallyNegativeLevy P 𝓕.rightCont)
    (hXY : Y.X = X.X)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) :
    IsAdmissibleLe Y x C D := by
  have hrisk (ω : Ω) (t : ℝ≥0) :
      riskProcess Y x D t ω = riskProcess X x D t ω := by
    simp only [riskProcess, hXY]
  have hruin (ω : Ω) :
      ruinTime Y x D ω = ruinTime X x D ω := by
    simp only [ruinTime, hrisk]
  constructor
  · constructor
    · exact dividendStrategy_rightCont_filtration D hD.1.1
    · intro ω t ht
      rw [hruin] at ht
      rw [hrisk]
      exact hD.1.2 ω t ht
  · intro ω t ht
    rw [hrisk]
    exact hD.2 ω t ht
