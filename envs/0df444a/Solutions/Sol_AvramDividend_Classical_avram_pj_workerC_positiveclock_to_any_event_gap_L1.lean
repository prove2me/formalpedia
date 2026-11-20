-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_positiveclock_to_any_event_gap_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:43:12.048168+00:00
-- url     : https://prove2.me/submissions/25de2e29-cef8-4525-be0b-c407abb438b0

import Mathlib
open MeasureTheory Set Filter Topology
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (A S : Set Ω) (hA : MeasurableSet A)
    (hS : MeasurableSet S) (G U : Ω → ℝ)
    (hGapI : Integrable (fun ω => G ω - U ω) P)
    (hZero : ∀ᵐ ω ∂P, ω ∉ S → G ω = U ω)
    (ε : ℝ)
    (hSsmall : (∫ ω in S,
      max (0 : ℝ) (G ω - U ω) ∂P) ≤ ε) :
    (∫ ω in A, max (0 : ℝ) (G ω - U ω) ∂P) ≤ ε := by 
  let f : Ω → ℝ := fun ω => max (0 : ℝ) (G ω - U ω)
  have hfI : Integrable f P := by
    have heq : f = fun ω => (|G ω - U ω| + (G ω - U ω)) / 2 := by
      funext ω
      dsimp [f]
      rcases le_total (0 : ℝ) (G ω - U ω) with hp | hp
      · rw [max_eq_right hp, abs_of_nonneg hp]
        ring
      · rw [max_eq_left hp, abs_of_nonpos hp]
        ring
    rw [heq]
    exact (hGapI.abs.add hGapI).div_const 2
  have hAI : Integrable (A.indicator f) P := hfI.indicator hA
  have hSI : Integrable (S.indicator f) P := hfI.indicator hS
  have hCompare : ∀ᵐ ω ∂P, A.indicator f ω ≤ S.indicator f ω := by
    filter_upwards [hZero] with ω hz
    by_cases ha : ω ∈ A
    · rw [Set.indicator_of_mem ha]
      by_cases hs : ω ∈ S
      · rw [Set.indicator_of_mem hs]
      · rw [Set.indicator_of_notMem hs]
        have hf0 : f ω = 0 := by
          dsimp [f]
          rw [hz hs]
          simp
        exact le_of_eq hf0
    · rw [Set.indicator_of_notMem ha]
      by_cases hs : ω ∈ S
      · rw [Set.indicator_of_mem hs]
        exact le_max_left _ _
      · rw [Set.indicator_of_notMem hs]
  have hIntegral := integral_mono_ae hAI hSI hCompare
  rw [integral_indicator hA, integral_indicator hS] at hIntegral
  exact hIntegral.trans hSsmall
