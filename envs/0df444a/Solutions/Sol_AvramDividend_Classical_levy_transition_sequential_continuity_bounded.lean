-- Prove2me | solution 1 for AvramDividend.Classical.levy_transition_sequential_continuity_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T21:28:26.899796+00:00
-- url     : https://prove2.me/submissions/36193fde-8c08-44d5-80bb-17be5c022239

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Process.Adapted
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0)
    (f : ℝ → ℝ) (hf : Continuous f)
    (B : ℝ) (hB : ∀ y : ℝ, ‖f y‖ ≤ B)
    (a : ℕ → ℝ) (x : ℝ)
    (ha : Filter.Tendsto a Filter.atTop (nhds x)) :
    Filter.Tendsto
      (fun n => ∫ ω, f (a n + X.X t ω) ∂P)
      Filter.atTop
      (nhds (∫ ω, f (x + X.X t ω) ∂P)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hXm : Measurable (X.X t) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hmeas (n : ℕ) :
      AEStronglyMeasurable (fun ω => f (a n + X.X t ω)) P := by
    exact (hf.measurable.comp (measurable_const.add hXm)).aestronglyMeasurable
  have hlim (ω : Ω) :
      Filter.Tendsto (fun n => f (a n + X.X t ω))
        Filter.atTop (nhds (f (x + X.X t ω))) := by
    have hshift : Filter.Tendsto (fun n => a n + X.X t ω)
        Filter.atTop (nhds (x + X.X t ω)) :=
      ha.add tendsto_const_nhds
    exact (hf.continuousAt.tendsto.comp hshift)
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun _ : Ω => B)
  · exact hmeas
  · exact integrable_const B
  · intro n
    filter_upwards [] with ω
    exact hB (a n + X.X t ω)
  · filter_upwards [] with ω
    exact hlim ω
