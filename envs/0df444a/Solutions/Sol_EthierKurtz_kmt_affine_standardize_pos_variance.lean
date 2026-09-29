-- Prove2me | solution 1 for EthierKurtz.kmt_affine_standardize_pos_variance
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T21:03:04.88299+00:00
-- url     : https://prove2.me/submissions/3fa94275-c008-4ce2-a3bd-42f877a56ea1

import Mathlib
import Theorems.Thm_EthierKurtz_affine_standardize_moments_of_pos_variance
import Theorems.Thm_EthierKurtz_affine_standardize_exp_moment

open MeasureTheory ProbabilityTheory

theorem solution
    (mu : ProbabilityMeasure Real)
    (hexp : Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
      Integrable (fun x : Real => Real.exp (a * x)) (mu : Measure Real)))
    (hvar : 0 < variance (fun x : Real => x) (mu : Measure Real)) :
    Exists fun (nu : ProbabilityMeasure Real) => Exists fun m : Real => Exists fun sigma : Real =>
      And (0 <= sigma) (And (Measure.map (fun y : Real => m + sigma * y) (nu : Measure Real) = (mu : Measure Real))
      (And (MeasureTheory.integral (nu : Measure Real) (fun y : Real => y) = 0)
      (And (variance (fun y : Real => y) (nu : Measure Real) = 1)
      (Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
        Integrable (fun y : Real => Real.exp (a * y)) (nu : Measure Real)))))) := by
  obtain ⟨nu, m, sigma, hsigma, hmap, hmean, hvariance⟩ :=
    EthierKurtz.affine_standardize_moments_of_pos_variance mu hvar
  obtain ⟨a0, ha0, hexp_nu⟩ :=
    EthierKurtz.affine_standardize_exp_moment mu nu m sigma hsigma hmap hexp
  exact ⟨nu, m, sigma, le_of_lt hsigma, hmap, hmean, hvariance, ⟨a0, ha0, hexp_nu⟩⟩
