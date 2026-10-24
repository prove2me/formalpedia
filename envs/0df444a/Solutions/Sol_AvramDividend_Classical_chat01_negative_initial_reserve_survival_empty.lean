-- Prove2me | solution 1 for AvramDividend.Classical.chat01_negative_initial_reserve_survival_empty
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:55:31.986435+00:00
-- url     : https://prove2.me/submissions/74ad47f1-250c-420e-9bd6-bd09accdadf2

import Mathlib.Data.NNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

/-- A negative initial reserve violates closed-horizon survival already at time zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : x < 0) (t : ℝ≥0) :
    {ω : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω} = ∅ := by
  ext ω
  constructor
  · intro hsurv
    have hzero : 0 ≤ x + X.X (0 : ℝ≥0) ω :=
      hsurv (0 : ℝ≥0) (by exact zero_le)
    simp only [X.X_zero ω, add_zero] at hzero
    exact (not_le_of_gt hx) hzero
  · simp
