-- Prove2me | solution 1 for AvramDividend.Classical.levy_capped_two_sided_first_exit_compensated_exponential_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T09:56:32.658452+00:00
-- url     : https://prove2.me/submissions/d376d0aa-5e0b-47c9-94f6-4399615725a2

import Theorems.Thm_AvramDividend_Classical_levy_capped_two_sided_first_exit_stopped_reserve_tendsto
import Theorems.Thm_AvramDividend_Classical_levy_capped_two_sided_first_exit_clock_tendsto
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Pathwise convergence of the capped compensated exponential at first exit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (first : ℕ → ℕ)
    (hfirst : ∀ᶠ n in atTop,
      (X.X ((first n : ℝ≥0) * mesh n) ω < lower ∨
       upper < X.X ((first n : ℝ≥0) * mesh n) ω) ∧
      (∀ j : ℕ, j < first n →
        ¬ (X.X ((j : ℝ≥0) * mesh n) ω < lower ∨
           upper < X.X ((j : ℝ≥0) * mesh n) ω)))
    (θ q : ℝ) :
    Tendsto (fun n =>
      let stop : ℝ≥0 := min ((first n : ℝ≥0) * mesh n) T
      Real.exp (θ * X.X stop ω - q * (stop : ℝ))) atTop
      (𝓝 (Real.exp (θ * X.X (min τ T) ω - q * ((min τ T : ℝ≥0) : ℝ)))) := by
  have hreserve :=
    levy_capped_two_sided_first_exit_stopped_reserve_tendsto
      X ω lower upper τ T hτ mesh hmesh hpos first hfirst
  have hclock :=
    levy_capped_two_sided_first_exit_clock_tendsto
      X ω lower upper τ T hτ mesh hmesh hpos first hfirst
  have htime : Tendsto (fun n =>
      ((min ((first n : ℝ≥0) * mesh n) T : ℝ≥0) : ℝ)) atTop
      (𝓝 (((min τ T : ℝ≥0) : ℝ))) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp hclock
  have harg : Tendsto (fun n =>
      θ * X.X (min ((first n : ℝ≥0) * mesh n) T) ω -
        q * ((min ((first n : ℝ≥0) * mesh n) T : ℝ≥0) : ℝ))
        atTop
      (𝓝 (θ * X.X (min τ T) ω - q * ((min τ T : ℝ≥0) : ℝ))) :=
    (tendsto_const_nhds.mul hreserve).sub (tendsto_const_nhds.mul htime)
  exact Real.continuous_exp.continuousAt.tendsto.comp harg
