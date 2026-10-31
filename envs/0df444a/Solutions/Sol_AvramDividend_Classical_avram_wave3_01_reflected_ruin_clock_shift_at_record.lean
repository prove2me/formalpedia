-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_reflected_ruin_clock_shift_at_record
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T08:53:02.836872+00:00
-- url     : https://prove2.me/submissions/84ec5b3b-22b1-4603-b417-2eaae5415851

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_firstBadClock_shift_of_no_early_breach
import Theorems.Thm_AvramDividend_Classical_firstRecord_drawdown_post_shift_reset
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_before_barrierRuin_iff_prefix_survival
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_barrierRuinTime_eq_strict_drawdown_subtype_clock

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- At a surviving true first record, the strict reflected ruin clock is
    the record time plus the exact restarted future drawdown clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hBefore : (u : ℝ≥0∞) < barrierRuinTime X a ω)
    (hBdd : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 u)) :
    barrierRuinTime X a ω =
      (u : ℝ≥0∞) +
        (⨅ i : {t : ℝ≥0 //
          X.X (u + t) ω -
            sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) < -a},
          (i.1 : ℝ≥0∞)) := by
  let bad : ℝ≥0 → Prop := fun s =>
    X.X s ω - runningSup X s ω < -a
  let shiftedBad : ℝ≥0 → Prop := fun t =>
    X.X (u + t) ω -
      sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) < -a
  have hprefix :=
    (firstUpcrossing_before_barrierRuin_iff_prefix_survival
      X a b ha hb ω u hu).mp hBefore
  have hpre : ∀ s : ℝ≥0, s < u → ¬ bad s := by
    intro s hs hbad
    have hsafe := hprefix s hs
    change runningSup X s ω - X.X s ω ≤ a at hsafe
    dsimp only [bad] at hbad
    linarith
  have hpost : ∀ t : ℝ≥0, bad (u + t) ↔ shiftedBad t := by
    intro t
    have hreset :=
      firstRecord_drawdown_post_shift_reset X b hb ω u hu hBdd t
    dsimp only [bad, shiftedBad]
    constructor <;> intro h <;> linarith
  have hshift :=
    firstBadClock_shift_of_no_early_breach u bad shiftedBad hpre hpost
  calc
    barrierRuinTime X a ω =
      (⨅ i : {s : ℝ≥0 // bad s}, (i.1 : ℝ≥0∞)) := by
        simpa only [bad] using
          (avram_root29_05_barrierRuinTime_eq_strict_drawdown_subtype_clock
            X a ω)
    _ = (u : ℝ≥0∞) +
      (⨅ i : {t : ℝ≥0 // shiftedBad t}, (i.1 : ℝ≥0∞)) := by
        simpa only [iInf_subtype] using hshift
    _ = _ := rfl
