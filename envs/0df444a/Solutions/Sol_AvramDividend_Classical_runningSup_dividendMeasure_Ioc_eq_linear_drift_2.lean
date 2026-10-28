-- Prove2me | solution 2 for AvramDividend.Classical.runningSup_dividendMeasure_Ioc_eq_linear_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:59:48.846011+00:00
-- url     : https://prove2.me/submissions/a71dc392-1751-4790-b50f-79d6f0565015

import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_rightLim
import Mathlib.Tactic.Ring
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (s t : ℝ)
    (hs : Function.rightLim
      (fun r : ℝ => runningSup X r.toNNReal ω) s = X.drift * s)
    (ht : Function.rightLim
      (fun r : ℝ => runningSup X r.toNNReal ω) t = X.drift * t) :
    (dividendMeasure (runningSup X) ω) (Ioc s t) =
      ENNReal.ofReal (X.drift * (t - s)) := by
  rw [runningSup_dividendMeasure_Ioc_rightLim, ht, hs]
  congr 1
  ring
