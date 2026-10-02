-- Prove2me | solution 1 for AvramDividend.BailOut.dStar_le_of_admissible
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T14:56:17.68621+00:00
-- url     : https://prove2.me/submissions/01902e6d-e61d-428d-b0b7-c0b977cbc9c1

import Mathlib
import Definitions.Def_AvramDividend_BailOut_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_BailOut_ScaleFunction
import Definitions.Def_AvramDividend_BailOut_BarrierCandidates

open MeasureTheory
open scoped NNReal ENNReal

open AvramDividend.BailOut in
theorem solution {q φ : ℝ} {W : ℝ → ℝ} {a : ℝ}
    (ha : 0 < a) (hG : Gfun q φ W a ≤ 0) :
    (dStar q φ W).toReal ≤ a := by
  have h : dStar q φ W ≤ ENNReal.ofReal a := by
    unfold dStar
    exact iInf_le_of_le a (iInf_le_of_le ha (iInf_le_of_le hG le_rfl))
  calc (dStar q φ W).toReal ≤ (ENNReal.ofReal a).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = a := ENNReal.toReal_ofReal ha.le
