-- Prove2me | solution 1 for AvramDividend.Classical.barrierFuture_iInf_prop_congr
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:12:04.664443+00:00
-- url     : https://prove2.me/submissions/7e8a729a-6193-42eb-ace3-88f1d00048dd

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {p q : Prop} (h : p ↔ q) (z : ℝ≥0∞) :
    (⨅ (_ : p), z) = ⨅ (_ : q), z := by
  rw [show p = q from propext h]
