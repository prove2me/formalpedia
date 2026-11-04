-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_source_cofinal_laplace_random_clock_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:09:56.707201+00:00
-- url     : https://prove2.me/submissions/27e581de-8396-4e9b-a429-8b34e5c92cd0

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

/-- Original BV drift-minus-real-jump series at an arbitrary sample-dependent
clock, inherited from the source all-horizon almost-sure event. -/
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
    (U : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P, X.X (U ω) ω = (U ω : ℝ) * X.drift -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ U ω then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal := by
  filter_upwards [avram_p3_a_bvdrift_original_cofinal_laplace_global_path
      X hBV T hT θ hθ hLap] with ω hPath
  exact hPath (U ω)