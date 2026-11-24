-- Prove2me | solution 1 for GaussianPerimeter.VolumeComparison.lintegral_fix_eq_lmarginal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:22:20.47412+00:00
-- url     : https://prove2.me/submissions/5d1e5a43-012c-4a2a-a655-955df1d48fe6

module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Definitions.Def_GaussianPerimeter_PrekopaHelpers
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Definitions.Def_GaussianPerimeter_PrekopaLeindler
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
theorem _root_.solution {d : ℕ}
    (F : (Fin (d + 2) → ℝ) → ENNReal) (x1 : Fin (d + 1) → ℝ)
    : ∫⁻ y : Fin 1 → ℝ, (fix F x1) y = (∫⋯∫⁻_{⟨d+1, by simp⟩}, F) (append x1 default) := by
  have h_lmarginal_singleton := lmarginal_singleton F ⟨d+1, by simp⟩ (μ := fun _ ↦ volume)
  suffices ∫⁻ (y : ℝ), F (Function.update (append x1 default) ⟨d + 1, by simp⟩ y)
      = ∫⁻ (y : Fin 1 → ℝ), fix F x1 y by
    rw [congrFun h_lmarginal_singleton (append x1 default), this]
  rw [lintegral_fin1]
  unfold fix append Function.update
  simp_all only [Pi.default_def, eq_rec_constant, Fin.default_eq_zero, Fin.isValue, dite_eq_ite,
    Function.comp_apply]
  congr; ext; congr; ext i; split
  case e_f.isTrue => simp_all
  case e_f.isFalse h => simp [Fin.val_lt_last h]
end GaussianPerimeter.VolumeComparison
