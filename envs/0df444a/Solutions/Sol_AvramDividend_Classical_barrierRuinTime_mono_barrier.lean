-- Prove2me | solution 1 for AvramDividend.Classical.barrierRuinTime_mono_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T19:26:16.630085+00:00
-- url     : https://prove2.me/submissions/cd7a1f8e-0151-4785-8127-f6e705b62ebb

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ) (hab : a ≤ b) (ω : Ω) :
    barrierRuinTime X a ω ≤ barrierRuinTime X b ω := by
  change (⨅ (t : ℝ≥0) (_ : a < drawdown X t ω), (t : ℝ≥0∞)) ≤
    (⨅ (t : ℝ≥0) (_ : b < drawdown X t ω), (t : ℝ≥0∞))
  refine le_iInf (fun t => ?_)
  refine le_iInf (fun hb => ?_)
  have ha : a < drawdown X t ω := lt_of_le_of_lt hab hb
  have hOuter :
      (⨅ (s : ℝ≥0) (_ : a < drawdown X s ω), (s : ℝ≥0∞)) ≤
      (⨅ (_ : a < drawdown X t ω), (t : ℝ≥0∞)) := by
    exact iInf_le
      (fun s : ℝ≥0 => ⨅ (_ : a < drawdown X s ω), (s : ℝ≥0∞)) t
  have hInner :
      (⨅ (_ : a < drawdown X t ω), (t : ℝ≥0∞)) ≤
      (t : ℝ≥0∞) := by
    exact iInf_le (fun (_ : a < drawdown X t ω) => (t : ℝ≥0∞)) ha
  exact hOuter.trans hInner
