-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_ae_stopped_L1_limit_preserves_zero_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:34:36.813071+00:00
-- url     : https://prove2.me/submissions/2b08f461-8af7-4aad-8319-186cd7a951af

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- The zero-mean property of stopped continuous-martingale Riemann sums
passes to their limit under explicit L1 convergence. This lemma never
asserts that an original Levy decomposition or that convergence exists. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → Ω → ℝ) (f : Ω → ℝ)
    (hf : AEStronglyMeasurable f P)
    (hFI : ∀ n, Integrable (F n) P)
    (hzero : ∀ n, (∫ ω, F n ω ∂P) = 0)
    (hL1 : Tendsto (fun n => ∫⁻ ω, ‖F n ω - f ω‖ₑ ∂P)
      atTop (nhds 0)) :
    (∫ ω, f ω ∂P) = 0 := by
  have ht : Tendsto (fun n => ∫ ω, F n ω ∂P) atTop
      (nhds (∫ ω, f ω ∂P)) := by
    exact MeasureTheory.tendsto_integral_of_L1 f hf
      (Filter.Eventually.of_forall hFI) hL1
  have hz : Tendsto (fun n => ∫ ω, F n ω ∂P) atTop
      (nhds (0 : ℝ)) := by
    have he : (fun n => ∫ ω, F n ω ∂P) =
        (fun _ : ℕ => (0 : ℝ)) := funext hzero
    rw [he]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique ht hz
