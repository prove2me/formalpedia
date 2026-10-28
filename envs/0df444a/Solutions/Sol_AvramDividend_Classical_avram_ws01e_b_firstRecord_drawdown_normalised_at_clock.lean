-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_firstRecord_drawdown_normalised_at_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T23:57:08.672292+00:00
-- url     : https://prove2.me/submissions/f5373f39-98b5-462a-a351-b0656d89500e

import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_firstRecord_drawdown_at_observation_clock
import Theorems.Thm_AvramDividend_Classical_shiftedSup_increment_eq_sup_sub
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- At a first strict upper record, terminal drawdown at a later observation
clock is a function of just the residual duration and the centred Lévy
increments after the record. This is the pathwise WH regeneration interface. -/
theorem solution
    {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞)))
    (hBdd : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 u))
    (e : Θ → ℝ≥0) (η : Θ) (hObs : u ≤ e η)
    (hShiftBdd : BddAbove
      ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 (e η - u))) :
    runningSup X (e η) ω - X.X (e η) ω =
      sSup ((fun r : ℝ≥0 =>
        X.X (u + r) ω - X.X u ω) '' Set.Icc 0 (e η - u)) -
      (X.X (e η) ω - X.X u ω) := by
  have hReset := avram_ws01e_b_firstRecord_drawdown_at_observation_clock
    X b hb ω u hu hBdd e η hObs
  have hTranslate := shiftedSup_increment_eq_sup_sub
    (fun r : ℝ≥0 => X.X r ω) u (e η - u) hShiftBdd
  rw [hReset, hTranslate]
  ring