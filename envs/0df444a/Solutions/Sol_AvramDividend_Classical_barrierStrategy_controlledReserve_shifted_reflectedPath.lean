-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_controlledReserve_shifted_reflectedPath
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:37:21.291575+00:00
-- url     : https://prove2.me/submissions/1b386e44-4756-4dcf-8309-5f5fa855cf39

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_at_firstUpcrossing_zero
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_after_firstUpcrossing_increment_eq_shiftedSup
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω) (u t : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞))) :
    riskProcess X x (barrierStrategy X x a) (u + t) ω =
      a + (X.X (u + t) ω - X.X u ω) -
        sSup ((fun r : ℝ≥0 => X.X (u + r) ω - X.X u ω) ''
          Set.Icc 0 t) := by
  have hXu := AvramDividend.Classical.firstUpcrossing_value_eq_threshold X (a - x) (by linarith) ω u hu
  have h0 := AvramDividend.Classical.barrierStrategy_at_firstUpcrossing_zero X x a hxa ω u hu
    (AvramDividend.Classical.levyPath_bddAbove_Icc X ω u)
  have hinc := AvramDividend.Classical.barrierStrategy_after_firstUpcrossing_increment_eq_shiftedSup
    X x a hxa ω u t hu (AvramDividend.Classical.levyPath_bddAbove_Icc X ω (u + t))
  unfold riskProcess
  linarith
