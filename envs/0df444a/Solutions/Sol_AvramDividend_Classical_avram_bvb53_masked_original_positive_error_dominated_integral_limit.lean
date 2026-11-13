-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb53_masked_original_positive_error_dominated_integral_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:41:32.202531+00:00
-- url     : https://prove2.me/submissions/23b94686-b10c-41e6-b836-6121b9657056

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (E : ℕ → Ω → ℝ) (A : Set Ω) (hA : MeasurableSet A)
    (hMeas : ∀ n, Measurable (E n))
    (K : Ω → ℝ) (hKI : Integrable K P)
    (hBound : ∀ n, ∀ᵐ ω ∂P,
      ‖if ω ∈ A then (0 : ℝ) else max (E n ω) 0‖ ≤ K ω)
    (hLim : ∀ᵐ ω ∂P,
      Tendsto (fun n => if ω ∈ A then (0 : ℝ)
        else max (E n ω) 0) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun n => ∫ ω,
      (if ω ∈ A then (0 : ℝ) else max (E n ω) 0) ∂P)
        atTop (𝓝 (0 : ℝ)) := by
  have hAE (n : ℕ) : AEStronglyMeasurable
      (fun ω : Ω => if ω ∈ A then (0 : ℝ) else max (E n ω) 0) P := by
    exact (Measurable.ite hA measurable_const ((hMeas n).max measurable_const)).aestronglyMeasurable
  simpa only [integral_zero] using
    (tendsto_integral_of_dominated_convergence K hAE hKI hBound hLim)
