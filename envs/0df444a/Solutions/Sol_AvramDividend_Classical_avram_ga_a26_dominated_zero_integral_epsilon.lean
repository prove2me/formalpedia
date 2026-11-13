-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a26_dominated_zero_integral_epsilon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:06:23.40029+00:00
-- url     : https://prove2.me/submissions/191593b8-7bdb-4ca3-a94b-17c060856611

import Mathlib.MeasureTheory.Integral.DominatedConvergence
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
noncomputable section

/-- Dominated a.e. convergence to zero gives uniform eventual absolute integral control. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hMeas : ∀ m, AEStronglyMeasurable (f m) P)
    (hG : Integrable g P)
    (hDom : ∀ m, ∀ᵐ ω ∂P, ‖f m ω‖ ≤ g ω)
    (hLim : ∀ᵐ ω ∂P, Tendsto (fun m => f m ω) atTop (nhds (0 : ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (f m) P ∧ (∫ ω, f m ω ∂P) ≤ ε := by
  have hIntegral :
      Tendsto (fun m : ℕ => ∫ ω, f m ω ∂P) atTop (nhds (0 : ℝ)) := by
    simpa using
      (MeasureTheory.tendsto_integral_of_dominated_convergence
        g hMeas hG hDom hLim)
  intro ε hε
  have hEventually : ∀ᶠ m : ℕ in atTop, (∫ ω, f m ω ∂P) < ε :=
    hIntegral.eventually (eventually_lt_nhds hε)
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.1 hEventually
  refine ⟨k, ?_⟩
  intro m hm
  have hI : Integrable (f m) P := hG.mono' (hMeas m) (hDom m)
  exact ⟨hI, (hk m hm).le⟩
