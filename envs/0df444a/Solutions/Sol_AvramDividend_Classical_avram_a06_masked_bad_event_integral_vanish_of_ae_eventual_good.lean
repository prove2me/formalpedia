-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_masked_bad_event_integral_vanish_of_ae_eventual_good
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T11:28:42.440634+00:00
-- url     : https://prove2.me/submissions/458012a7-0b5f-4dc9-aadf-cd80b3515d5e

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped Topology Classical
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (H : Ω → ℝ) (hHm : Measurable H) (hHI : Integrable H P)
    (s : ℕ → Set Ω) (hs : ∀ n, MeasurableSet (s n))
    (hEventually : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ s n) :
    Tendsto (fun n : ℕ => ∫ ω, (if ω ∈ s n then (0 : ℝ) else H ω) ∂P)
      atTop (𝓝 (0 : ℝ))  := by
  have hFMeas (n : ℕ) :
      AEStronglyMeasurable
        (fun ω : Ω => if ω ∈ s n then (0 : ℝ) else H ω) P := by
    exact (Measurable.ite (hs n) measurable_const hHm).aestronglyMeasurable
  have hDom (n : ℕ) : ∀ᵐ ω ∂P,
      ‖if ω ∈ s n then (0 : ℝ) else H ω‖ ≤ |H ω| := by
    filter_upwards [] with ω
    by_cases hω : ω ∈ s n
    · simp [hω]
    · simp [hω, Real.norm_eq_abs]
  have hLim : ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => if ω ∈ s n then (0 : ℝ) else H ω)
        atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hEventually] with ω hω
    refine (tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [hω] with n hn
    simp [hn]
  have hDCT := MeasureTheory.tendsto_integral_of_dominated_convergence
    (F := fun n ω => if ω ∈ s n then (0 : ℝ) else H ω)
    (f := fun _ => (0 : ℝ)) (fun ω => |H ω|)
    hFMeas hHI.abs hDom hLim
  simpa using hDCT
