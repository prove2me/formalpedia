-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_ruinTime_post_firstUpcrossing_add_shifted_badClock
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:28:36.263474+00:00
-- url     : https://prove2.me/submissions/b25452b3-0502-402f-8c38-88736ed70190

import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_firstBadClock_shift_of_no_early_breach
import Theorems.Thm_AvramDividend_Classical_riskProcess_post_firstUpcrossing_ruin_iff
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (hsuccess : (u : ℝ≥0∞) <
      ruinTime X x (barrierStrategy X x a) ω) :
    ruinTime X x (barrierStrategy X x a) ω =
      (u : ℝ≥0∞) +
        (⨅ (t : ℝ≥0)
          (_ : a + (X.X (u + t) ω - X.X u ω) <
            max 0
              (sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
                X.X u ω)), (t : ℝ≥0∞)) := by
  unfold ruinTime
  apply firstBadClock_shift_of_no_early_breach
  · intro s hs hbad
    have : ruinTime X x (barrierStrategy X x a) ω ≤ (s : ℝ≥0∞) := iInf₂_le s hbad
    have hs' : (s : ℝ≥0∞) < u := by exact_mod_cast hs
    exact absurd (hsuccess.trans_le this) (not_lt.2 hs'.le)
  · intro t
    exact riskProcess_post_firstUpcrossing_ruin_iff X x a hxa u t ω hu
      (levyPath_bddAbove_Icc X ω (u + t))
