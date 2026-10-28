-- Prove2me | solution 1 for AvramDividend.Classical.barrierRuinTime_zero_of_near_zero_drawdown
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T20:19:21.195976+00:00
-- url     : https://prove2.me/submissions/f7d838c7-e6c3-4c36-80b8-5bbff745351b

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Arbitrarily early strict drawdowns force the reflected first-ruin infimum to vanish. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a : ℝ) (ω : Ω)
    (hNear : ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ a < drawdown X t ω) :
    barrierRuinTime X a ω = 0 := by
  apply le_antisymm ?_ bot_le
  by_contra hn
  have hpos : (0 : ℝ≥0∞) < barrierRuinTime X a ω :=
    lt_of_not_ge hn
  obtain ⟨ε, hε0, hεRuin⟩ :=
    ENNReal.lt_iff_exists_nnreal_btwn.mp hpos
  have hεpos : (0 : ℝ≥0) < ε := by
    exact_mod_cast hε0
  obtain ⟨t, htε, hdraw⟩ := hNear ε hεpos
  have hLe : barrierRuinTime X a ω ≤ (t : ℝ≥0∞) := by
    change (⨅ (s : ℝ≥0) (_ : a < drawdown X s ω), (s : ℝ≥0∞)) ≤
      (t : ℝ≥0∞)
    have hOuter :
        (⨅ (s : ℝ≥0) (_ : a < drawdown X s ω), (s : ℝ≥0∞)) ≤
        (⨅ (_ : a < drawdown X t ω), (t : ℝ≥0∞)) :=
      iInf_le
        (fun s : ℝ≥0 => ⨅ (_ : a < drawdown X s ω), (s : ℝ≥0∞)) t
    have hInner :
        (⨅ (_ : a < drawdown X t ω), (t : ℝ≥0∞)) ≤
        (t : ℝ≥0∞) :=
      iInf_le (fun (_ : a < drawdown X t ω) => (t : ℝ≥0∞)) hdraw
    exact hOuter.trans hInner
  have htε' : (t : ℝ≥0∞) < (ε : ℝ≥0∞) := by
    exact_mod_cast htε
  exact lt_asymm hεRuin (lt_of_le_of_lt hLe htε')