-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_barrierRuinTime_eq_strict_drawdown_subtype_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T15:14:19.240648+00:00
-- url     : https://prove2.me/submissions/65f74511-7caf-4f06-a4c8-40bfb5a85908

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_Reflection
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- The canonical reflected-barrier ruin stopping time is the genuine first
strict drawdown threshold clock in the original Lévy process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a : ℝ) (ω : Ω) :
    barrierRuinTime X a ω =
      (⨅ i : {t : ℝ≥0 // X.X t ω - runningSup X t ω < -a},
        (i.1 : ℝ≥0∞)) := by
  have hEvent (t : ℝ≥0) :
      (a < runningSup X t ω - X.X t ω) ↔
      (X.X t ω - runningSup X t ω < -a) := by
    constructor <;> intro h <;> linarith
  simp [barrierRuinTime, drawdown, reflectedSup, iInf_subtype, hEvent]
