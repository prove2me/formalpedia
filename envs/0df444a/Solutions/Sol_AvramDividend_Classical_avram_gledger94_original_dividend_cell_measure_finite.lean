-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger94_original_dividend_cell_measure_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:29:03.665365+00:00
-- url     : https://prove2.me/submissions/21dc717a-53eb-451d-9c4f-ee4dc730abd8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_locallyFinite
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (a b : ℝ) :
    dividendMeasure D ω (Ioc a b) ≠ ⊤ := by
  letI : IsLocallyFiniteMeasure (dividendMeasure D ω) :=
    dividendMeasure_locallyFinite D ω
  have hlt : dividendMeasure D ω (Ioc a b) < ⊤ := by
    exact measure_Ioc_lt_top
  exact ne_of_lt hlt
