-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_shifted_runningSup_dividendMeasure_Ioc_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:57:28.17044+00:00
-- url     : https://prove2.me/submissions/7b3cee69-e781-44d7-8bff-213840d22bdb

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_shifted_runningSup_dividendMeasure_Ioc
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Unconditional Stieltjes window translation along a first barrier upcrossing. -/
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
          ω) (Set.Ioc (0 : ℝ) (t : ℝ)) := by
  intro t
  exact barrierStrategy_shifted_runningSup_dividendMeasure_Ioc
    X x a hxa ω u hu t (levyPath_bddAbove_Icc X ω (u + t))
