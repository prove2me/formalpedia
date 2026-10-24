-- Prove2me | solution 1 for AvramDividend.Classical.chat04_future_window_killed_scale_integrable_of_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:49:27.843908+00:00
-- url     : https://prove2.me/submissions/9596e2f6-47fa-45a5-a9ea-0a08559c7505

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_standing_scale_fixed_time_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-! The future-window killed discounted scale payoff is integrable whenever
its pathwise survival event is measurable, under the original Standing axioms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u)
    (hB : MeasurableSet
      {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}) :
    Integrable
      (({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
        (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
          W (x + X.X u ω))) P := by
  have hScale : Integrable (fun ω => W (x + X.X u ω)) P :=
    AvramDividend.Classical.chat04_standing_scale_fixed_time_integrable
      X hX q hq W hW x u
  have hDiscounted : Integrable
      (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
        W (x + X.X u ω)) P :=
    hScale.const_mul (Real.exp (-(q * ((u : ℝ) - (s : ℝ)))))
  exact hDiscounted.indicator hB
