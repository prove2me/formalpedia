-- Prove2me | solution 1 for GaussianPerimeter.VolumeComparison.lintegral_fin1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:09:12.367835+00:00
-- url     : https://prove2.me/submissions/ad80e87d-765b-4ad0-8714-f6b9ce411c3b

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
theorem _root_.solution (F : (Fin 1 → ℝ) → ENNReal) :
    ∫⁻ v : (Fin 1 → ℝ), F v = ∫⁻ x : ℝ, F (fun _ ↦ x) := by
  exact MeasurePreserving.lintegral_map_equiv F _ (volume_preserving_funUnique (Fin 1) ℝ).symm
end GaussianPerimeter.VolumeComparison
