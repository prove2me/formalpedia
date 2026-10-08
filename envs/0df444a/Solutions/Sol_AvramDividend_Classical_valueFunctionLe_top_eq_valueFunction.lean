-- Prove2me | solution 1 for AvramDividend.Classical.valueFunctionLe_top_eq_valueFunction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:37:20.017601+00:00
-- url     : https://prove2.me/submissions/d17d1781-f36d-4f6e-ae8a-5ba194f22d5b

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ) :
    valueFunctionLe X q (⊤ : ℝ≥0∞) x = valueFunction X q x := by
  simp [valueFunctionLe, valueFunction, IsAdmissibleLe]
