-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_l2_conditional_centering_closed_under_band_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:26:46.255318+00:00
-- url     : https://prove2.me/submissions/5c93f3b5-5db1-4bd4-8c98-dac208e2355e

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (mPast : MeasurableSpace Ω)
    (hPast : mPast ≤ mΩ)
    [@SigmaFinite Ω mPast (P.trim hPast)]
    (M : ℕ → Lp ℝ (2 : ℝ≥0∞) P)
    (Mlimit : Lp ℝ (2 : ℝ≥0∞) P)
    (hconv : Tendsto M Filter.atTop (nhds Mlimit))
    (hcenter : ∀ n, (MeasureTheory.condExpL2 ℝ ℝ hPast) (M n) = 0) :
    (MeasureTheory.condExpL2 ℝ ℝ hPast) Mlimit = 0 := by
  have hlim :
      Tendsto (fun n => (MeasureTheory.condExpL2 ℝ ℝ hPast) (M n))
        Filter.atTop (nhds ((MeasureTheory.condExpL2 ℝ ℝ hPast) Mlimit)) :=
    ((MeasureTheory.condExpL2 ℝ ℝ hPast).continuous.tendsto Mlimit).comp hconv
  have hlimzero :
      Tendsto (fun n => (MeasureTheory.condExpL2 ℝ ℝ hPast) (M n))
        Filter.atTop (nhds 0) := by
    simp [hcenter]
  exact tendsto_nhds_unique hlim hlimzero
