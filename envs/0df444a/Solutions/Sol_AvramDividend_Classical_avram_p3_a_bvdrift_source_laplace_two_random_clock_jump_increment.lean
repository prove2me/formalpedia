-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_source_laplace_two_random_clock_jump_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:10:05.739149+00:00
-- url     : https://prove2.me/submissions/9bd72a01-637a-46dd-9ddd-60746d69ad8c

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_cofinal_laplace_global_path

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The original BV path increment between arbitrary sample-dependent clocks
is physical drift less the difference of genuine negative left-jump totals. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℕ → ℝ≥0) (hT : ∀ t : ℝ≥0, ∃ n, t ≤ T n)
    (θ : ℝ) (hθ : 1 ≤ θ)
    (hLap : ∀ n : ℕ,
      (∫ ω : Ω, Real.exp (-(θ * (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T n then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal)) ∂P) =
        Real.exp (-(T n : ℝ) *
          (∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂X.ν)))
    (S U : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P, X.X (U ω) ω - X.X (S ω) ω =
      ((U ω : ℝ) - (S ω : ℝ)) * X.drift -
      ((∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ U ω then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal - (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ S ω then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal) := by
  filter_upwards [avram_p3_a_bvdrift_original_cofinal_laplace_global_path
      X hBV T hT θ hθ hLap] with ω hPath
  rw [hPath (U ω), hPath (S ω)]
  ring