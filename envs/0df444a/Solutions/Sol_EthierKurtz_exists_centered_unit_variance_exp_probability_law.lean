-- Prove2me | solution 1 for EthierKurtz.exists_centered_unit_variance_exp_probability_law
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T05:39:42.422552+00:00
-- url     : https://prove2.me/submissions/c5737ce6-7d81-4750-afb4-c7797f6cda4e

import Mathlib

open MeasureTheory ProbabilityTheory in
theorem solution :
    Exists fun (nu : ProbabilityMeasure Real) =>
      And (MeasureTheory.integral (nu : Measure Real) (fun y : Real => y) = 0)
      (And (variance (fun y : Real => y) (nu : Measure Real) = 1)
      (Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
        Integrable (fun y : Real => Real.exp (a * y)) (nu : Measure Real)))) := by
  refine ⟨⟨gaussianReal 0 1, inferInstance⟩, ?_, ?_, 1, one_pos, fun a _ => ?_⟩
  · exact integral_id_gaussianReal
  · simp
  · exact integrable_exp_mul_gaussianReal a
