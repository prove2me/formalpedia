-- Prove2me | solution 1 for AvramDividend.Classical.dividendMeasure_locallyFinite
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:55:02.570689+00:00
-- url     : https://prove2.me/submissions/68b02fd9-2964-42ca-bd79-9dfcfa80effd

import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    IsLocallyFiniteMeasure (dividendMeasure D ω) := by
  unfold dividendMeasure
  split_ifs
  · infer_instance
  · infer_instance
