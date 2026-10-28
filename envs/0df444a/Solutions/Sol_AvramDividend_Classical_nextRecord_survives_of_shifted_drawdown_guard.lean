-- Prove2me | solution 1 for AvramDividend.Classical.nextRecord_survives_of_shifted_drawdown_guard
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T18:14:45.636994+00:00
-- url     : https://prove2.me/submissions/9de56488-8625-42f3-a561-b67777040972

import Mathlib.Data.Real.Basic
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstRecord_prefix_survival_concat
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_strictly_before_drawdown_ruin
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! A safe future preserves the next finite killed record after past survival. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (ω : Ω) (u v T : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hv : (v : ℝ≥0∞) = twoSidedExitUpTime X (b + ε) ω)
    (hvT : v ≤ u + T)
    (hPre : ∀ r : ℝ≥0, r < u → reflectedSup X r ω ≤ a)
    (hPost : ∀ t : ℝ≥0, t ≤ T →
      sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
        X.X (u + t) ω ≤ a) :
    (v : ℝ≥0∞) < barrierRuinTime X a ω := by
  have hBdd := levyPath_bddAbove_Icc X ω u
  have hAll :=
    firstRecord_prefix_survival_concat
      X b hb ω u hu hBdd a T hPre hPost
  have hNextPre : ∀ r : ℝ≥0, r < v → reflectedSup X r ω ≤ a := by
    intro r hr
    exact hAll r (lt_of_lt_of_le hr hvT)
  have hbNext : 0 ≤ b + ε := add_nonneg hb hε
  have hv' : (v : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b + ε < X.X s ω), (s : ℝ≥0∞)) := hv
  exact firstUpcrossing_strictly_before_drawdown_ruin
    X a (b + ε) ha hbNext ω v hv' hNextPre
