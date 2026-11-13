-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a26_spatial_integrable_from_physical_plus_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:16:18.113958+00:00
-- url     : https://prove2.me/submissions/121dbac9-64b6-4fd5-a882-8bd0e8e3bc1e

import Mathlib.MeasureTheory.Function.L1Space.Integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A B : Ω → ℝ)
    (hA : Integrable (fun ω => |A ω|) P)
    (hPhysical : Integrable (fun ω => max (A ω + B ω) (0 : ℝ)) P)
    (hMeas : AEStronglyMeasurable (fun ω => max (B ω) (0 : ℝ)) P) :
    Integrable (fun ω => max (B ω) (0 : ℝ)) P := by
  have hcontrol := hPhysical.add hA
  apply hcontrol.mono' hMeas
  filter_upwards [] with ω
  have hbound : max (B ω) 0 ≤ max (A ω + B ω) 0 + |A ω| := by
    apply max_le
    · linarith [le_max_left (A ω + B ω) (0 : ℝ), neg_le_abs (A ω)]
    · exact add_nonneg (le_max_right _ _) (abs_nonneg _)
  have hl : 0 ≤ max (B ω) (0 : ℝ) := le_max_right _ _
  have hr : 0 ≤ max (A ω + B ω) 0 + |A ω| :=
    add_nonneg (le_max_right _ _) (abs_nonneg _)
  simpa [Real.norm_eq_abs, abs_of_nonneg hl, abs_of_nonneg hr] using hbound
