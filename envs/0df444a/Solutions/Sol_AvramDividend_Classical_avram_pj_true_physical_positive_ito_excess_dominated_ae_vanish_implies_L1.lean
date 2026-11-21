-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_true_physical_positive_ito_excess_dominated_ae_vanish_implies_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T17:46:48.631014+00:00
-- url     : https://prove2.me/submissions/8c6ae094-62d8-4bdb-83f6-0d7c0694d662

import Mathlib
open MeasureTheory Filter Topology
noncomputable section

/-- A genuinely measurable dominated original physical-grid positive
Itô excess that tends to zero almost everywhere vanishes in L1. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : ℕ → Ω → ℝ)
    (hFI : ∀ k, Integrable (F k) P)
    (B : Ω → ℝ) (hBI : Integrable B P)
    (hDom : ∀ k, ∀ᵐ ω ∂P, |F k ω| ≤ B ω)
    (hAE : ∀ᵐ ω ∂P,
      Tendsto (fun k => F k ω) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun k => ∫ ω, |F k ω| ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  have hConv :
      Tendsto (fun k => ∫ ω, |F k ω| ∂P)
        atTop (𝓝 (∫ ω, (0 : ℝ) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence B
    · intro k
      exact (hFI k).abs.aestronglyMeasurable
    · exact hBI
    · intro k
      filter_upwards [hDom k] with ω h
      simpa only [Real.norm_eq_abs, abs_abs] using h
    · filter_upwards [hAE] with ω h
      simpa only [abs_zero] using h.abs
  simpa only [integral_zero] using hConv
