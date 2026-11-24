-- Prove2me | solution 1 for GaussianPerimeter.VolumeComparison.append_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:08:57.171813+00:00
-- url     : https://prove2.me/submissions/e4b45779-ac05-4fc8-a294-f7045b6cfd56

module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Definitions.Def_GaussianPerimeter_PrekopaHelpers
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Definitions.Def_GaussianPerimeter_PrekopaLeindler

set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter GaussianPerimeter.VolumeComparison
open MeasureTheory Set
open scoped Pointwise
namespace GaussianPerimeter.VolumeComparison
theorem _root_.solution {d : ℕ} (x : Fin d → ℝ) : Measurable (append x) := by
  unfold append
  apply measurable_pi_lambda
  intro i
  split_ifs <;> fun_prop
end GaussianPerimeter.VolumeComparison
