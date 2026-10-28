-- Prove2me | solution 1 for AvramDividend.Classical.chat04_positive_reserve_scale_expectation_nhds_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:25:05.113129+00:00
-- url     : https://prove2.me/submissions/747fe37c-8953-40a7-b4af-7bb0ec989626

import Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_deterministic_scale_expectation_tendsto
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal

/-- Initial-time continuity of the real expected q-scale reward,
obtained from sequential L² convergence and first countability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ) (hx : 0 < x) :
    Filter.Tendsto
      (fun t : ℝ≥0 => ∫ ω,
        Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω) ∂P)
      (𝓝 0) (𝓝 (W x)) := by
  apply (Filter.tendsto_iff_seq_tendsto).2
  intro u hu
  obtain ⟨N, hN⟩ := hu.bddAbove_range
  have hBound : ∀ n, u n ≤ N := by
    intro n
    exact hN (Set.mem_range_self n)
  have h := chat04_positive_reserve_deterministic_scale_expectation_tendsto
    X q hq W hW θ x hθ hψ hx N u hBound hu
  simpa only [Function.comp_def] using h