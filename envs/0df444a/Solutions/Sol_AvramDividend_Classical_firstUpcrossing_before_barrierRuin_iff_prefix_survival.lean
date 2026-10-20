-- Prove2me | solution 1 for AvramDividend.Classical.firstUpcrossing_before_barrierRuin_iff_prefix_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T13:21:19.595334+00:00
-- url     : https://prove2.me/submissions/5d74d910-b503-4de5-bf3f-70334046e6a2

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_strictly_before_drawdown_ruin

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
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞))) :
    (u : ℝ≥0∞) < barrierRuinTime X a ω ↔
      ∀ t : ℝ≥0, t < u → reflectedSup X t ω ≤ a := by
  constructor
  · intro hBefore t ht
    by_contra hSafe
    have hBad : a < reflectedSup X t ω := lt_of_not_ge hSafe
    have hInf : barrierRuinTime X a ω ≤ (t : ℝ≥0∞) := by
      change (⨅ (s : ℝ≥0) (_ : a < drawdown X s ω),
        (s : ℝ≥0∞)) ≤ (t : ℝ≥0∞)
      have hAt : (⨅ (_ : a < drawdown X t ω),
          (t : ℝ≥0∞)) ≤ (t : ℝ≥0∞) := by
        exact iInf_le
          (fun (_ : a < drawdown X t ω) => (t : ℝ≥0∞)) hBad
      have hOuter :
          (⨅ (s : ℝ≥0) (_ : a < drawdown X s ω),
            (s : ℝ≥0∞)) ≤
          (⨅ (_ : a < drawdown X t ω), (t : ℝ≥0∞)) := by
        exact iInf_le
          (fun s : ℝ≥0 => ⨅ (_ : a < drawdown X s ω),
            (s : ℝ≥0∞)) t
      exact hOuter.trans hAt
    have hTU : (t : ℝ≥0∞) < (u : ℝ≥0∞) :=
      ENNReal.coe_lt_coe.mpr ht
    exact (not_lt_of_ge hInf) (hTU.trans hBefore)
  · intro hPrefix
    exact firstUpcrossing_strictly_before_drawdown_ruin
      X a b ha hb ω u hu hPrefix
