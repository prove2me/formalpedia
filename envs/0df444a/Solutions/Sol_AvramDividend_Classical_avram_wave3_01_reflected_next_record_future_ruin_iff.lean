-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_reflected_next_record_future_ruin_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:24:07.293673+00:00
-- url     : https://prove2.me/submissions/71c0fd92-9289-402a-941e-20857e02e41c

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_attains_peak
import Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_eq_add_shifted_inf
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_reflected_ruin_clock_shift_at_record

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The surviving next-record event is exactly the shifted-future reflected
    survival event, even when the next clock or ruin clock is infinite. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hBefore : (u : ℝ≥0∞) < barrierRuinTime X a ω)
    (hBdd : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 u)) :
    (twoSidedExitUpTime X (b + c) ω < barrierRuinTime X a ω) ↔
      (⨅ i : {t : ℝ≥0 //
          c < X.X (u + t) ω - X.X u ω}, (i.1 : ℝ≥0∞)) <
      (⨅ i : {t : ℝ≥0 //
          X.X (u + t) ω -
            sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) < -a},
        (i.1 : ℝ≥0∞)) := by
  have hAt : X.X u ω = b :=
    (firstUpcrossing_attains_peak X b hb ω u
      (by simpa only [twoSidedExitUpTime] using hu)).1
  have hNext :=
    nextRecord_upclock_eq_add_shifted_inf X b c hc u ω hu hAt
  have hRuin :=
    avram_wave3_01_reflected_ruin_clock_shift_at_record
      X a b ha hb ω u hu hBefore hBdd
  rw [hNext, hRuin]
  simp only [iInf_subtype]
  exact ENNReal.add_lt_add_iff_left
    (ne_of_lt (lt_of_lt_of_le hBefore le_top))
