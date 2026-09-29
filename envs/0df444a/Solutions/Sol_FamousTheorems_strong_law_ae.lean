-- Prove2me | solution 1 for FamousTheorems.strong_law_ae
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T23:06:17.019876+00:00
-- url     : https://prove2.me/submissions/3b8f3f68-a8e6-41cd-bbd6-e8f252d36ee8

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped Real Topology

theorem solution {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (X : ℕ → Ω → E) (hint : Integrable (X 0) μ)
    (hindep : Pairwise (Function.onFun (· ⟂ᵢ[μ] ·) X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, X i ω)) atTop
      (𝓝 μ[X 0]) :=
  ProbabilityTheory.strong_law_ae X hint hindep hident
