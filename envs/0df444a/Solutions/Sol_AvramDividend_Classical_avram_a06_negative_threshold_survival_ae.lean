-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_negative_threshold_survival_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T15:56:41.216805+00:00
-- url     : https://prove2.me/submissions/2ccd0ee5-77d7-4c61-a1b0-9ca896948ca3

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (R : Ω → ℝ) (hPos : ∀ᵐ ω ∂P, 0 < R ω)
    (u : ℝ) (hu : u < 0) :
    ∀ᵐ ω ∂P, (u < R ω ↔ 0 < R ω) := by
  filter_upwards [hPos] with ω hω
  exact ⟨fun _ => hω, fun hp => lt_trans hu hp⟩
