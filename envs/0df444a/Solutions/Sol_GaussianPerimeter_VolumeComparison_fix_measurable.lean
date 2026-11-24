-- Prove2me | solution 1 for GaussianPerimeter.VolumeComparison.fix_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:10:38.258834+00:00
-- url     : https://prove2.me/submissions/99d87d4a-a2ba-4333-8a05-45aefe3cc244

module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Definitions.Def_GaussianPerimeter_PrekopaHelpers
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Definitions.Def_GaussianPerimeter_PrekopaLeindler
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_append_measurable
public import Theorems.Thm_P2M_GaussianPerimeter_VolumeComparison_append_measurable__f5f150faf8d6
attribute [local fun_prop] GaussianPerimeter.VolumeComparison.append_measurable
attribute [local fun_prop] GaussianPerimeter.VolumeComparison.append_measurable'

set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter GaussianPerimeter.VolumeComparison
open MeasureTheory Set
open scoped Pointwise
namespace GaussianPerimeter.VolumeComparison
theorem _root_.solution {d : ℕ} {F : (Fin (d + 1) → ℝ) → ENNReal} (hF : Measurable F) (x : Fin d → ℝ)
    : Measurable (fix F x) := by
  unfold fix
  fun_prop
end GaussianPerimeter.VolumeComparison
