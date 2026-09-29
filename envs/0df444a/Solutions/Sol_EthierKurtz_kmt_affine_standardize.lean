-- Prove2me | solution 1 for EthierKurtz.kmt_affine_standardize
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T20:49:03.588632+00:00
-- url     : https://prove2.me/submissions/337f54de-f7c1-464f-810a-e2fbcb809303

import Mathlib
import Theorems.Thm_EthierKurtz_kmt_affine_standardize_pos_variance
import Theorems.Thm_EthierKurtz_kmt_affine_standardize_zero_variance

open MeasureTheory ProbabilityTheory

theorem solution
    (mu : ProbabilityMeasure Real)
    (hexp : Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
      Integrable (fun x : Real => Real.exp (a * x)) (mu : Measure Real))) :
    Exists fun (nu : ProbabilityMeasure Real) => Exists fun m : Real => Exists fun sigma : Real =>
      And (0 <= sigma) (And (Measure.map (fun y : Real => m + sigma * y) (nu : Measure Real) = (mu : Measure Real))
      (And (MeasureTheory.integral (nu : Measure Real) (fun y : Real => y) = 0)
      (And (variance (fun y : Real => y) (nu : Measure Real) = 1)
      (Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
        Integrable (fun y : Real => Real.exp (a * y)) (nu : Measure Real)))))) := by
  by_cases hvar : variance (fun x : Real => x) (mu : Measure Real) = 0
  · exact EthierKurtz.kmt_affine_standardize_zero_variance mu hexp hvar
  · have hpos : 0 < variance (fun x : Real => x) (mu : Measure Real) :=
      lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm hvar)
    exact EthierKurtz.kmt_affine_standardize_pos_variance mu hexp hpos