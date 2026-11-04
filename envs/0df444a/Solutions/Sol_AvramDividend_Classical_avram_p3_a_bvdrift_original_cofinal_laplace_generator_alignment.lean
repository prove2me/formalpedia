-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_cofinal_laplace_generator_alignment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:42:41.249891+00:00
-- url     : https://prove2.me/submissions/c4480c57-436b-4e4d-a2bf-6c83504fea5c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_cofinal_laplace_global_intervals

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Source BV physical drift identifies both the exact generator coefficient
and genuine original-process all-interval pathwise negative-jump budget. -/
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
    (w : ℝ → ℝ) (x : ℝ) (hGen : X.GeneratorIntegrable w x) :
    (X.generator w x = X.drift * deriv w x +
      ∫ y in Iio (0 : ℝ), w (x + y) - w x ∂X.ν) ∧
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t →
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
  exact ⟨boundedVariation_generator_physical_drift_representation
    X hBV w x hGen,
    avram_p3_a_bvdrift_original_cofinal_laplace_global_intervals
      X hBV T hT θ hθ hLap⟩
