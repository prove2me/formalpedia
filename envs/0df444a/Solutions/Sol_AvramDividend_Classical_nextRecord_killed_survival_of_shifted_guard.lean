-- Prove2me | solution 1 for AvramDividend.Classical.nextRecord_killed_survival_of_shifted_guard
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T18:20:27.626488+00:00
-- url     : https://prove2.me/submissions/9adbca87-8e0b-4361-8b34-65701bde7d2b

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_before_barrierRuin_iff_prefix_survival
import Theorems.Thm_AvramDividend_Classical_nextRecord_survives_of_shifted_drawdown_guard
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Killed record survival persists through a safe shifted future. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (ω : Ω) (u v T : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hv : (v : ℝ≥0∞) = twoSidedExitUpTime X (b + ε) ω)
    (hBefore : (u : ℝ≥0∞) < barrierRuinTime X a ω)
    (hvT : v ≤ u + T)
    (hPost : ∀ t : ℝ≥0, t ≤ T →
      sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
        X.X (u + t) ω ≤ a) :
    (v : ℝ≥0∞) < barrierRuinTime X a ω := by
  have hu' : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞)) := hu
  have hPre : ∀ r : ℝ≥0, r < u → reflectedSup X r ω ≤ a :=
    (firstUpcrossing_before_barrierRuin_iff_prefix_survival
      X a b ha hb ω u hu').1 hBefore
  exact nextRecord_survives_of_shifted_drawdown_guard
    X a b ε ha hb hε ω u v T hu hv hvT hPre hPost
