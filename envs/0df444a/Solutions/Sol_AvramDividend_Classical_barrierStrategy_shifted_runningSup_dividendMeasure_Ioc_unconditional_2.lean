-- Prove2me | solution 2 for AvramDividend.Classical.barrierStrategy_shifted_runningSup_dividendMeasure_Ioc_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:58:32.051091+00:00
-- url     : https://prove2.me/submissions/a5a4efe2-efaa-4a86-912e-cf388f7fea4f

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_shifted_runningSup_dividendMeasure_Ioc
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) (hxa : x ≤ a)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞))) :
    ∀ t : ℝ≥0,
      (dividendMeasure (barrierStrategy X x a) ω)
          (Set.Ioc (u : ℝ) ((u + t : ℝ≥0) : ℝ)) =
        (dividendMeasure
          (fun r _ =>
            sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
          ω) (Set.Ioc (0 : ℝ) (t : ℝ)) := fun t =>
  AvramDividend.Classical.barrierStrategy_shifted_runningSup_dividendMeasure_Ioc X x a hxa ω u hu t
    (AvramDividend.Classical.levyPath_bddAbove_Icc X ω (u + t))
