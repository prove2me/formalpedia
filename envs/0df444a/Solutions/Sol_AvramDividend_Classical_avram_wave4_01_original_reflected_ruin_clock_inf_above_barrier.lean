-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_reflected_ruin_clock_inf_above_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:59:33.124919+00:00
-- url     : https://prove2.me/submissions/d3ed4b04-a075-4615-a05e-cf6b151b0bf0

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_mono_barrier
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_barrierRuinTime_eq_strict_drawdown_subtype_clock
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

/-- True strict reflected ruin is the infimum over strictly higher barriers. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a : ℝ) (ω : Ω) :
    barrierRuinTime X a ω =
      ⨅ b : {b : ℝ // a < b}, barrierRuinTime X b.1 ω := by
  apply le_antisymm
  · apply le_iInf
    intro b
    exact barrierRuinTime_mono_barrier X a b.1 (le_of_lt b.2) ω
  · rw [avram_root29_05_barrierRuinTime_eq_strict_drawdown_subtype_clock X a ω]
    apply le_iInf
    intro i
    let b : ℝ := (a + (runningSup X i.1 ω - X.X i.1 ω)) / 2
    have hb1 : a < b := by
      dsimp [b]
      linarith [i.2]
    have hb2 : X.X i.1 ω - runningSup X i.1 ω < -b := by
      dsimp [b]
      linarith [i.2]
    have hhit : barrierRuinTime X b ω ≤ (i.1 : ℝ≥0∞) := by
      rw [avram_root29_05_barrierRuinTime_eq_strict_drawdown_subtype_clock X b ω]
      exact iInf_le _ (⟨i.1, hb2⟩ :
        {t : ℝ≥0 // X.X t ω - runningSup X t ω < -b})
    calc
      (⨅ s : {s : ℝ // a < s}, barrierRuinTime X s.1 ω) ≤
          barrierRuinTime X b ω :=
            iInf_le _ (⟨b, hb1⟩ : {s : ℝ // a < s})
      _ ≤ (i.1 : ℝ≥0∞) := hhit
