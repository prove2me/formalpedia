-- Prove2me | solution 1 for AvramDividend.Classical.excursion_lintegral_limit_of_strict_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:55:20.474502+00:00
-- url     : https://prove2.me/submissions/1be985f5-be53-46ba-9133-761e593a17ec

import Mathlib.MeasureTheory.Measure.Prokhorov
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology

/-!
A strictly increasing subsequence preserves a sequence limit.  The
uniqueness of limits in ENNReal identifies the limiting measure's
integral after weak convergence supplies its subsequential limit.
-/
theorem solution
    (β : ℕ → Measure ℝ) (μ : Measure ℝ) (g : ℝ → ENNReal)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (L : ENNReal)
    (hfull : Tendsto (fun n : ℕ => ∫⁻ x, g x ∂β n) atTop (𝓝 L))
    (hsub : Tendsto (fun n : ℕ => ∫⁻ x, g x ∂β (φ n)) atTop
      (𝓝 (∫⁻ x, g x ∂μ))) :
    (∫⁻ x, g x ∂μ) = L := by
  have hfullsub : Tendsto
      (fun n : ℕ => ∫⁻ x, g x ∂β (φ n)) atTop (𝓝 L) := by
    simpa only [Function.comp_def] using
      hfull.comp hφ.tendsto_atTop
  exact tendsto_nhds_unique hsub hfullsub
