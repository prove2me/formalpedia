-- Prove2me | solution 1 for AvramDividend.Classical.reflectedSup_origin_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:45:58.278324+00:00
-- url     : https://prove2.me/submissions/14a593bb-4ad0-474e-8ef5-13da6362d295

import Definitions.Def_AvramDividend_Classical_Reflection
import Mathlib.Order.Interval.Set.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    reflectedSup X 0 ω = 0 := by
  have hS0 : runningSup X 0 ω = 0 := by
    unfold runningSup
    have hu : ∀ u : Icc (0 : ℝ≥0) 0, X.X u ω = 0 := fun u => by
      have hs : (u : ℝ≥0) = 0 := le_antisymm u.2.2 u.2.1
      rw [hs, X.X_zero]
    simp [hu, maxZero]
  simp [reflectedSup, hS0, X.X_zero ω]
