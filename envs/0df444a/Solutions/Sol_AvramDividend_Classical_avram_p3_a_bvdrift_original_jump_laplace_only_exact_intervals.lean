-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_jump_laplace_only_exact_intervals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:02:46.282827+00:00
-- url     : https://prove2.me/submissions/f7681681-6cb0-42af-baf8-af36fac509ad

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_actual_jump_exponential_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_jump_laplace_gives_exact_intervals

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Under the genuine source jump Laplace identity, BV intervals have
exactly source physical drift minus actual intrinsic negative jump mass.
Both exponential integrability facts are proved for the original process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (θ : ℝ) (hθ : 1 ≤ θ)
    (hJLap : (∫ ω : Ω, Real.exp (-(θ * (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal)) ∂P) =
      Real.exp (-(T : ℝ) *
        (∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂X.ν))) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      X.X t ω - X.X s ω =
        ((t : ℝ) - (s : ℝ)) * X.drift -
        (∫⁻ p,
          (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
          ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u)))).toReal := by
  have hθ0 : 0 ≤ θ := by linarith only [hθ]
  have hJInt :=
    avram_p3_a_bvdrift_actual_jump_exponential_integrable X hBV T θ hθ0
  exact avram_p3_a_bvdrift_original_jump_laplace_gives_exact_intervals
    X hBV T θ hθ hJInt hJLap
