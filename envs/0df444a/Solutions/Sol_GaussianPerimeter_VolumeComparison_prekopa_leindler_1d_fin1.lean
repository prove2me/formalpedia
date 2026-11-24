-- Prove2me | solution 1 for GaussianPerimeter.VolumeComparison.prekopa_leindler_1d_fin1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:26:38.813671+00:00
-- url     : https://prove2.me/submissions/95433776-1efe-4fb8-a43d-3bb596cec0e6

module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Definitions.Def_GaussianPerimeter_PrekopaHelpers
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Definitions.Def_GaussianPerimeter_PrekopaLeindler
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_prekopa_leindler_1d
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_lintegral_fin1
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_append_measurable
public import Theorems.Thm_P2M_GaussianPerimeter_VolumeComparison_append_measurable__f5f150faf8d6
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_fix_measurable
attribute [local fun_prop] GaussianPerimeter.VolumeComparison.append_measurable
attribute [local fun_prop] GaussianPerimeter.VolumeComparison.append_measurable'
attribute [local fun_prop] GaussianPerimeter.VolumeComparison.fix_measurable

set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter GaussianPerimeter.VolumeComparison
open MeasureTheory Set
open scoped Pointwise
namespace GaussianPerimeter.VolumeComparison
theorem _root_.solution
    {θ : ℝ} {f g h : (Fin 1 → ℝ) → ENNReal} (hθfgh : PLConditions 1 θ f g h)
    : ENNReal.ofReal ((1-θ)^(1-θ) * θ^θ)⁻¹ * (∫⁻ x, f x)^(1-θ) * (∫⁻ x, g x)^θ ≤ ∫⁻ x, h x := by
  let ⟨hθ0, hθ1, hf_measurable, hg_measurable, hh_measurable, hfgh⟩ := hθfgh
  rw [lintegral_fin1 f, lintegral_fin1 g, lintegral_fin1 h]
  exact prekopa_leindler_1d
    ⟨hθ0, hθ1⟩
    (by fun_prop)
    (by fun_prop)
    (by fun_prop)
    (fun x y ↦ hfgh (fun _ ↦ x) (fun _ ↦ y))
end GaussianPerimeter.VolumeComparison
