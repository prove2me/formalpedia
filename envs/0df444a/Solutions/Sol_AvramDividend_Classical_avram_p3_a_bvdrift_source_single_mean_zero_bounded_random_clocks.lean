-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_source_single_mean_zero_bounded_random_clocks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:10:30.899208+00:00
-- url     : https://prove2.me/submissions/44837e30-9492-4cc9-9dfb-09b2f77d0a08

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_any_BV_single_moment_exact_original_intervals

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- One finite-horizon actual-source BV Laplace or residual moment condition
transfers the full marked negative-jump budget to ordered random clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0)
    (hIntegrable : Integrable (fun ω : Ω =>
      ((T : ℝ) * X.drift - X.X T ω) -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal) P)
    (hMeanZero : (∫ ω : Ω,
      (((T : ℝ) * X.drift - X.X T ω) -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal) ∂P) = 0)
    (S U : Ω → ℝ≥0)
    (hSU : ∀ᵐ ω ∂P, S ω ≤ U ω)
    (hUT : ∀ᵐ ω ∂P, U ω ≤ T) :
    ∀ᵐ ω ∂P, X.X (U ω) ω - X.X (S ω) ω =
        ((U ω : ℝ) - (S ω : ℝ)) * X.drift -
        (∫⁻ p,
          (if S ω < p.1 ∧ p.1 ≤ U ω then ENNReal.ofReal (-p.2) else 0) ∂
          ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u)))).toReal := by
  filter_upwards [avram_p3_a_bvdrift_any_BV_single_moment_exact_original_intervals
      X hBV T hIntegrable hMeanZero, hSU, hUT] with ω hPath hClock hBound
  exact hPath (S ω) (U ω) hClock hBound