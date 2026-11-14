-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb65_positive_dominated_residual_eventual_expected_epsilon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T17:20:58.361204+00:00
-- url     : https://prove2.me/submissions/82f70fad-2e0c-48ee-9ad5-fa418c166e1d

import Mathlib.MeasureTheory.Integral.DominatedConvergence
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped Topology
noncomputable section

/-- Bochner dominated convergence supplies the cofinal expected budget. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : ℕ → Ω → ℝ) (H : Ω → ℝ)
    (hMeas : ∀ n, AEStronglyMeasurable (E n) P)
    (hInt : Integrable H P)
    (hDom : ∀ n, ∀ᵐ ω ∂P, ‖E n ω‖ ≤ H ω)
    (hAE : ∀ᵐ ω ∂P, Tendsto (fun n => E n ω) atTop (𝓝 (0 : ℝ))) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in (atTop : Filter ℕ), (∫ ω, E n ω ∂P) ≤ ε := by
  have hLimit : Tendsto (fun n => ∫ ω, E n ω ∂P) atTop (𝓝 (0 : ℝ)) := by
    simpa only [integral_zero] using
      (MeasureTheory.tendsto_integral_of_dominated_convergence
        H hMeas hInt hDom hAE)
  intro ε hε
  have hEventually := hLimit.eventually (Iio_mem_nhds hε)
  filter_upwards [hEventually] with n hn
  exact le_of_lt hn
