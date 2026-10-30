-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_shifted_future_raw_ruin_eq_strict_drawdown_subtype_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T15:54:16.945664+00:00
-- url     : https://prove2.me/submissions/1d6a4f55-43fd-4abb-aa8a-710105e6e5cc

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_shiftedLevy_ruin_threshold_iff_increment_runningSup

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- The exact future ruin clock used by the true barrier dividend
Stieltjes formula equals strict drawdown of the shifted increment record. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (age : ℝ≥0) (a : ℝ) :
    (⨅ (r : ℝ≥0)
      (_ : a + (X.X (age + r) ω - X.X age ω) <
        max 0
          (sSup ((fun z : ℝ≥0 => X.X (age + z) ω) '' Icc 0 r) -
            X.X age ω)), (r : ℝ≥0∞)) =
    (⨅ i : {r : ℝ≥0 //
       (X.X (age + r) ω - X.X age ω) -
       sSup ((fun z : ℝ≥0 => X.X (age + z) ω - X.X age ω) ''
         Icc 0 r) < -a}, (i.1 : ℝ≥0∞)) := by
  have hEvent (r : ℝ≥0) :
      (a + (X.X (age + r) ω - X.X age ω) <
        max 0
          (sSup ((fun z : ℝ≥0 => X.X (age + z) ω) '' Icc 0 r) -
            X.X age ω)) ↔
      ((X.X (age + r) ω - X.X age ω) -
        sSup ((fun z : ℝ≥0 => X.X (age + z) ω - X.X age ω) ''
          Icc 0 r) < -a) := by
    rw [shiftedLevy_ruin_threshold_iff_increment_runningSup X a ω age r]
    constructor <;> intro h <;> linarith
  simp [iInf_subtype, hEvent]
