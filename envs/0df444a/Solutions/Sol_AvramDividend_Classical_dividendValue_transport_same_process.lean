-- Prove2me | solution 1 for AvramDividend.Classical.dividendValue_transport_same_process
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T19:25:22.577042+00:00
-- url     : https://prove2.me/submissions/6542d59b-be64-45f0-9f3e-f88be7e339a2

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
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
    (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) :
    dividendValue Y q x D = dividendValue X q x D := by
  simp only [dividendValue, ruinTime, riskProcess, hXY]
