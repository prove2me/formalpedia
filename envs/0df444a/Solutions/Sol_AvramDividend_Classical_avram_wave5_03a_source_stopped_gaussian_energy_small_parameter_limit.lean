-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_source_stopped_gaussian_energy_small_parameter_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:06:39.80712+00:00
-- url     : https://prove2.me/submissions/4b5230a7-73b1-407b-90e9-8b0d1ed08578

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_source_gaussian_stopped_exponential_rescaled_energy_export
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_exp_energy_slope_right

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Actual stopped source Gaussian difference-quotient variance tends to h sigma squared. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) :
    Filter.Tendsto (fun ε : ℝ => (∫ ω,
      ((Real.exp (Real.sqrt ε *
          (X.X (τ ω + h) ω - X.X (τ ω) ω) -
          (h : ℝ) * X.ψ (Real.sqrt ε)) - 1) /
            Real.sqrt ε) ^ 2 ∂P))
      (𝓝[>] (0 : ℝ)) (𝓝 ((h : ℝ) * X.σ ^ 2)) := by
  let A : ℝ := (h : ℝ) * X.σ ^ 2
  have hslope :
      Filter.Tendsto (fun ε : ℝ => (Real.exp (A * ε) - 1) / ε)
        (𝓝[>] (0 : ℝ)) (𝓝 A) :=
    avram_wave5_03a_exp_energy_slope_right A
  have heq :
      (fun ε : ℝ => (∫ ω,
      ((Real.exp (Real.sqrt ε *
          (X.X (τ ω + h) ω - X.X (τ ω) ω) -
          (h : ℝ) * X.ψ (Real.sqrt ε)) - 1) /
            Real.sqrt ε) ^ 2 ∂P)) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun ε : ℝ => (Real.exp (A * ε) - 1) / ε) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hs : (Real.sqrt ε) ^ 2 = ε :=
      Real.sq_sqrt (le_of_lt hε)
    rw [avram_wave5_03a_source_gaussian_stopped_exponential_rescaled_energy_export
      X hν τ hτ T hbounded h (Real.sqrt ε) (Real.sqrt_nonneg ε)]
    rw [hs]
    dsimp [A]
    congr 2
    ring
  exact hslope.congr' heq.symm