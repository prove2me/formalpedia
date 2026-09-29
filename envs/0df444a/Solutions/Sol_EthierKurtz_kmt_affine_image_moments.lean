-- Prove2me | solution 1 for EthierKurtz.kmt_affine_image_moments
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T01:15:46.913845+00:00
-- url     : https://prove2.me/submissions/c10b240b-1085-4ca1-bc3a-50c1396139ab

import Mathlib
import Definitions.Def_EthierKurtz_kmtApproximation

open MeasureTheory ProbabilityTheory EthierKurtz in
theorem solution
    (mu nu : ProbabilityMeasure Real) (m sig : Real)
    (hmap : Measure.map (fun y : Real => m + sig * y) (nu : Measure Real) = (mu : Measure Real))
    (hmean : MeasureTheory.integral (nu : Measure Real) (fun y : Real => y) = 0)
    (hvariance : variance (fun y : Real => y) (nu : Measure Real) = 1) :
    MeasureTheory.integral (mu : Measure Real) (fun y : Real => y) = m /\
      variance (fun y : Real => y) (mu : Measure Real) = sig ^ 2 := by
  have hmeas : Measurable (fun y : Real => m + sig * y) := by fun_prop
  have hLp : MemLp (fun y : Real => y) 2 (nu : Measure Real) :=
    memLp_two_of_variance_ne_zero measurable_id.aestronglyMeasurable
      (by rw [hvariance]; exact one_ne_zero)
  have hint : Integrable (fun y : Real => y) (nu : Measure Real) :=
    hLp.integrable one_le_two
  refine ⟨?_, ?_⟩
  · rw [← hmap, integral_map hmeas.aemeasurable (by fun_prop)]
    rw [integral_add (integrable_const m) (hint.const_mul sig), integral_const,
      integral_const_mul, hmean]
    simp
  · rw [← hmap]
    have h1 := variance_id_map (μ := (nu : Measure Real)) hmeas.aemeasurable
    have h2 := variance_const_add (μ := (nu : Measure Real))
      (X := fun y : Real => sig * y) (by fun_prop) m
    have h3 := variance_const_mul sig (fun y : Real => y) (nu : Measure Real)
    calc variance (fun y : Real => y) (Measure.map (fun y : Real => m + sig * y) (nu : Measure Real))
        = variance (fun y : Real => m + sig * y) (nu : Measure Real) := h1
      _ = variance (fun y : Real => sig * y) (nu : Measure Real) := h2
      _ = sig ^ 2 * variance (fun y : Real => y) (nu : Measure Real) := h3
      _ = sig ^ 2 := by rw [hvariance, mul_one]

