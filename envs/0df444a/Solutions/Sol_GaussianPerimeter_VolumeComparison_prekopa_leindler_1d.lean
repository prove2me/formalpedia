-- Prove2me | solution 1 for GaussianPerimeter.VolumeComparison.prekopa_leindler_1d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:25:52.950142+00:00
-- url     : https://prove2.me/submissions/dc4cfd88-82bf-4439-b6d0-c89f26ab51c4

module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Definitions.Def_GaussianPerimeter_PrekopaHelpers
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Definitions.Def_GaussianPerimeter_PrekopaLeindler
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_prekopa_leindler_1d_bounded
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_iSup_min_nat
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_iSup_min_nat_ne_top
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_iSup_rpow_of_pos


set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter GaussianPerimeter.VolumeComparison
open MeasureTheory Set
open scoped Pointwise
namespace GaussianPerimeter.VolumeComparison
theorem _root_.solution {θ : ℝ} {f g h : ℝ → ENNReal}
    (hθ : 0 < θ ∧ θ < 1)
    (hf_measurable : Measurable f)
    (hg_measurable : Measurable g)
    (hh_measurable : Measurable h)
    (hfgh : ∀ x y, (f x) ^ (1 - θ) * (g y) ^ θ ≤ h (x + y))
    : ENNReal.ofReal ((1-θ)^(1-θ) * θ^θ)⁻¹ * (∫⁻ x, f x)^(1-θ) * (∫⁻ x, g x)^θ ≤ ∫⁻ x, h x := by
  let c : ENNReal := ENNReal.ofReal ((1-θ)^(1-θ) * θ^θ)⁻¹
  let f_bounded (n : ℕ) : ℝ → ENNReal := fun x ↦ min (f x) n
  let g_bounded (n : ℕ) : ℝ → ENNReal := fun x ↦ min (g x) n

  have f_bounded_mono : Monotone f_bounded := by
    intro _ _ hab; rw [Pi.le_def]; intro x; exact min_le_min_left (f x) (by simp [hab])
  have g_bounded_mono : Monotone g_bounded := by
    intro _ _ hab; rw [Pi.le_def]; intro x; exact min_le_min_left (g x) (by simp [hab])

  have f_as_sup : ∫⁻ x, f x = ⨆ n, ∫⁻ x, f_bounded n x := calc
    _ = ∫⁻ x, ⨆ n, f_bounded n x := by congr; ext; symm; apply iSup_min_nat
    _ = _ := lintegral_iSup (by fun_prop) f_bounded_mono
  have g_as_sup : ∫⁻ x, g x = ⨆ n, ∫⁻ x, g_bounded n x := calc
    _ = ∫⁻ x, ⨆ n, g_bounded n x := by congr; ext; symm; apply iSup_min_nat
    _ = _ := lintegral_iSup (by fun_prop) g_bounded_mono

  have result_for_bounded : ∀ n m,
      c * (∫⁻ x, f_bounded n x)^(1-θ) * (∫⁻ x, g_bounded m x)^θ ≤ ∫⁻ x, h x := by
    intro n m
    apply prekopa_leindler_1d_bounded hθ (by fun_prop) (iSup_min_nat_ne_top n _)
      (by fun_prop) (iSup_min_nat_ne_top m _) hh_measurable
    intro x y
    calc
      (f_bounded n x)^(1-θ) * (g_bounded m y)^θ ≤ (f x)^(1-θ) * (g y)^θ := by
        gcongr
        · linarith
        · aesop
        · linarith
        aesop
      _ ≤ h (x + y) := hfgh x y

  calc
    c * (∫⁻ x, f x)^(1-θ) * (∫⁻ x, g x)^θ
        = c * (⨆ n, ∫⁻ x, f_bounded n x)^(1-θ) * (⨆ m, ∫⁻ x, g_bounded m x)^θ := by
      rw [f_as_sup, g_as_sup]
    _ = ⨆ n, c * (∫⁻ x, f_bounded n x)^(1-θ) * (⨆ m, ∫⁻ x, g_bounded m x)^θ := by
      rw [← ENNReal.iSup_mul, ← ENNReal.mul_iSup, iSup_rpow_of_pos (by linarith)]
    _ = ⨆ n, ⨆ m, c * (∫⁻ x, f_bounded n x)^(1-θ) * (∫⁻ x, g_bounded m x)^θ := by
      congr; ext; rw [← ENNReal.mul_iSup, iSup_rpow_of_pos hθ.1]
    _ ≤ ∫⁻ x, h x := by apply iSup₂_le; exact result_for_bounded
end GaussianPerimeter.VolumeComparison
