-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_scale_expectation_rightContinuous_of_uniform_l2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:47:09.065446+00:00
-- url     : https://prove2.me/submissions/8a9bbf48-8f26-4dc5-8e7b-6bfd88201b8a

import Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_expectation_tendsto_of_uniform_l2
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal

/-- Killed q-scale expectations are right-continuous at every horizon,
    by sequential continuity and uniform finite-horizon second moments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ) (t₀ : ℝ≥0) :
    ContinuousWithinAt
      (fun t : ℝ≥0 => ∫ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => Real.exp (-(q * (t : ℝ))) *
            W (x + X.X t u)) ω ∂P)
      (Ici t₀) t₀ := by
  change Tendsto
    (fun t : ℝ≥0 => ∫ ω,
      ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
        (fun u => Real.exp (-(q * (t : ℝ))) *
          W (x + X.X t u)) ω ∂P)
    (𝓝[Ici t₀] t₀)
    (𝓝 (∫ ω,
      ({u : Ω | ∀ s : ℝ≥0, s ≤ t₀ → 0 ≤ x + X.X s u}).indicator
        (fun u => Real.exp (-(q * (t₀ : ℝ))) *
          W (x + X.X t₀ u)) ω ∂P))
  apply (Filter.tendsto_iff_seq_tendsto).2
  intro u hu
  have hu0 : Tendsto u atTop (𝓝 t₀) :=
    hu.mono_right nhdsWithin_le_nhds
  obtain ⟨N, hN⟩ := hu0.bddAbove_range
  have hBound : ∀ n, u n ≤ N :=
    fun n => hN (Set.mem_range_self n)
  have h := chat04_killed_scale_expectation_tendsto_of_uniform_l2
    X q hq W hW hzero θ x hθ hψ N t₀ u hBound hu
  simpa only [Function.comp_def] using h
