-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_dividendMeasure_Ioc_eq_linear_drift
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:59:04.661344+00:00
-- url     : https://prove2.me/submissions/ecd26f4e-8a40-4430-b604-7ad01438212b

import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_rightLim
import Mathlib.Tactic.Ring
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
  rw [runningSup_dividendMeasure_Ioc_rightLim, hs, ht, mul_sub]
