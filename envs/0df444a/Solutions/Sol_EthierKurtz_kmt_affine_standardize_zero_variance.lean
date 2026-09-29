-- Prove2me | solution 1 for EthierKurtz.kmt_affine_standardize_zero_variance
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T21:11:16.317711+00:00
-- url     : https://prove2.me/submissions/c0d3885e-5056-46de-bff6-4aa49fd571be

import Mathlib
import Theorems.Thm_EthierKurtz_kmt_zero_variance_measure_is_dirac
import Theorems.Thm_EthierKurtz_exists_centered_unit_variance_exp_probability_law
open MeasureTheory ProbabilityTheory

theorem solution
    (mu : ProbabilityMeasure Real)
    (hexp : Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
      Integrable (fun x : Real => Real.exp (a * x)) (mu : Measure Real)))
    (hvar : variance (fun x : Real => x) (mu : Measure Real) = 0) :
    Exists fun (nu : ProbabilityMeasure Real) => Exists fun m : Real => Exists fun sigma : Real =>
      And (0 <= sigma) (And (Measure.map (fun y : Real => m + sigma * y) (nu : Measure Real) = (mu : Measure Real))
      (And (MeasureTheory.integral (nu : Measure Real) (fun y : Real => y) = 0)
      (And (variance (fun y : Real => y) (nu : Measure Real) = 1)
      (Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
        Integrable (fun y : Real => Real.exp (a * y)) (nu : Measure Real)))))) := by
  let hpoint := EthierKurtz.kmt_zero_variance_measure_is_dirac mu hexp hvar
  let m := Exists.choose hpoint
  have hm := Exists.choose_spec hpoint
  let hstd := EthierKurtz.exists_centered_unit_variance_exp_probability_law
  let nu : ProbabilityMeasure Real := Exists.choose hstd
  have hstd_prop := Exists.choose_spec hstd
  have hmean : MeasureTheory.integral (nu : Measure Real) (fun y : Real => y) = 0 := by
    simpa [nu] using hstd_prop.left
  have hvarnu : variance (fun y : Real => y) (nu : Measure Real) = 1 := by
    simpa [nu] using hstd_prop.right.left
  have hexpnu : Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
      Integrable (fun y : Real => Real.exp (a * y)) (nu : Measure Real)) := by
    simpa [nu] using hstd_prop.right.right
  have hdirac : Measure.dirac m = (mu : Measure Real) := by
    simpa [m, Measure.map_const] using hm
  have hconst : (fun y : Real => m + 0 * y) = fun _ : Real => m := by
    funext y
    ring
  apply Exists.intro nu
  apply Exists.intro m
  apply Exists.intro 0
  apply And.intro le_rfl
  apply And.intro
  case left =>
    rw [hconst]
    simpa [Measure.map_const] using hdirac
  case right =>
    exact And.intro hmean (And.intro hvarnu hexpnu)
