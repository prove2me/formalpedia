-- Prove2me | solution 1 for AvramDividend.Classical.countable_capped_grid_superlevel_isStoppingTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T20:38:03.284837+00:00
-- url     : https://prove2.me/submissions/6d330be7-aba2-4cf9-8505-9a892287e51b

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsRightContinuous]
    (u : ℝ≥0 → Ω → ℝ) (hu : Adapted 𝓕 u)
    (clock : ℕ → ℝ≥0) (H : ℝ≥0)
    (hclock : ∀ n : ℕ, clock n ≤ H) (x : ℝ) :
    IsStoppingTime 𝓕 (fun ω : Ω =>
      ⨅ n : ℕ, if x ≤ u (clock n) ω
        then (clock n : WithTop ℝ≥0) else (H : WithTop ℝ≥0)) := by
  have hEach (n : ℕ) :
      IsStoppingTime 𝓕
        (fun ω : Ω => if x ≤ u (clock n) ω
          then (clock n : WithTop ℝ≥0) else (H : WithTop ℝ≥0)) := by
    have hEvent : MeasurableSet[𝓕 (clock n)]
        {ω : Ω | x ≤ u (clock n) ω} :=
      measurableSet_le measurable_const (hu (clock n))
    have hPiece := isStoppingTime_piecewise_const (hclock n) hEvent
    change IsStoppingTime 𝓕
      (fun ω : Ω => if x ≤ u (clock n) ω
        then (clock n : WithTop ℝ≥0) else (H : WithTop ℝ≥0)) at hPiece
    exact hPiece
  exact IsStoppingTime.iInf hEach
