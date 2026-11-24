-- Prove2me | solution 1 for GaussianPerimeter.VolumeComparison.prekopa_leindler_1d_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:24:03.740538+00:00
-- url     : https://prove2.me/submissions/d63bbbfb-8c03-40c6-9877-da03da802000

module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Definitions.Def_GaussianPerimeter_PrekopaHelpers
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Definitions.Def_GaussianPerimeter_PrekopaLeindler
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_prekopa_leindler_1d_normalized
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_iSup_nonzero_of_nonzero


set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter GaussianPerimeter.VolumeComparison
open MeasureTheory Set
open scoped Pointwise
namespace GaussianPerimeter.VolumeComparison
theorem _root_.solution {θ : ℝ} {f g h : ℝ → ENNReal}
    (hθ : 0 < θ ∧ θ < 1)
    (hf_measurable : Measurable f) (hf_bounded : iSup f ≠ ⊤)
    (hg_measurable : Measurable g) (hg_bounded : iSup g ≠ ⊤)
    (hh_measurable : Measurable h)
    (hfgh : ∀ x y, (f x) ^ (1 - θ) * (g y) ^ θ ≤ h (x + y))
    : ENNReal.ofReal (((1-θ)^(1-θ) * θ^θ)⁻¹) * (∫⁻ x, f x)^(1-θ) * (∫⁻ x, g x)^θ ≤ ∫⁻ x, h x := by

  -- If f = 0 or g = 0, the conclusion follows easily.
  by_cases hf_zero : f = 0
  · aesop
  by_cases hg_zero : g = 0
  · aesop

  -- From here on, we have f ≠ 0 and g ≠ 0.
  let f' := fun x ↦ (f x) * (iSup f)⁻¹
  let g' := fun x ↦ (g x) * (iSup g)⁻¹
  let h' := fun x ↦ (h x) * ((iSup f)⁻¹)^(1-θ) * ((iSup g)⁻¹)^θ
  let fint := ∫⁻ x, f x
  let gint := ∫⁻ x, g x
  let hint := ∫⁻ x, h x
  let f'int := ∫⁻ x, f' x
  let g'int := ∫⁻ x, g' x
  let h'int := ∫⁻ x, h' x
  let factor : ENNReal := ENNReal.ofReal ((1-θ)^(1-θ) * θ^θ)⁻¹

  have iSupf_ne_zero : iSup f ≠ 0 := iSup_nonzero_of_nonzero hf_zero
  have iSupg_ne_zero : iSup g ≠ 0 := iSup_nonzero_of_nonzero hg_zero
  have iSupf_pos : 0 < iSup f := pos_of_ne_zero iSupf_ne_zero
  have iSupg_pos : 0 < iSup g := pos_of_ne_zero iSupg_ne_zero
  have iSupf_pow_ne_zero : (iSup f)^(1-θ) ≠ 0 :=
    (ne_of_lt (ENNReal.rpow_pos_of_nonneg iSupf_pos (by linarith))).symm
  have iSupg_pow_ne_zero : (iSup g)^θ ≠ 0 :=
    (ne_of_lt (ENNReal.rpow_pos_of_nonneg iSupg_pos (by linarith))).symm
  have iSupf_pow_ne_top : (iSup f)^(1-θ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg' iSupf_pos hf_bounded
  have iSupg_pow_ne_top : (iSup g)^θ ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg' iSupg_pos hg_bounded

  -- This is the result for the normalized functions f', g', h'.
  have normalized_result : factor * f'int^(1-θ) * g'int^θ ≤ h'int :=
    have f'_isup1 : iSup f' = 1 := by
      rw [← ENNReal.iSup_mul, ENNReal.mul_inv_cancel iSupf_ne_zero hf_bounded]
    have g'_isup1 : iSup g' = 1 := by
      rw [← ENNReal.iSup_mul, ENNReal.mul_inv_cancel iSupg_ne_zero hg_bounded]
    have hf'g'h' : ∀ x y, (f' x)^(1-θ) * (g' y)^θ ≤ h' (x + y) := by
      unfold f' g' h'
      intro x y
      calc
        (f x * (iSup f)⁻¹) ^ (1 - θ) * (g y * (iSup g)⁻¹) ^ θ
            = (f x)^(1 - θ) * ((iSup f)⁻¹) ^ (1 - θ) * (g y) ^ θ * ((iSup g)⁻¹)^θ := by
          rw [ENNReal.mul_rpow_of_nonneg, ENNReal.mul_rpow_of_nonneg]
          · ring
          · linarith
          linarith
        _ = (f x)^(1 - θ) * (g y) ^ θ * ((iSup f)⁻¹) ^ (1 - θ) * ((iSup g)⁻¹)^θ := by ring
        _ ≤ h' (x + y) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hfgh x y) (by apply zero_le)) (by apply zero_le)
    prekopa_leindler_1d_normalized
      hθ
      (by fun_prop) f'_isup1
      (by fun_prop) g'_isup1
      (by fun_prop)
      hf'g'h'

  -- Manipulate the constant factors in normalized_result to obtain the final result for f, g, h.
  have f'int_to_fint : f'int = fint * (iSup f)⁻¹ := lintegral_mul_const (iSup f)⁻¹ hf_measurable
  have g'int_to_gint : g'int = gint * (iSup g)⁻¹ := lintegral_mul_const (iSup g)⁻¹ hg_measurable
  have h'int_to_hint : h'int = hint * (iSup f)⁻¹^(1-θ) * (iSup g)⁻¹^θ := calc
    h'int = ∫⁻ x, ((h x) * (iSup f)⁻¹^(1-θ) * (iSup g)⁻¹^θ) := by rfl
    _ = ∫⁻ x, ((h x) * ((iSup f)⁻¹^(1-θ) * (iSup g)⁻¹^θ)) := by congr; ext x; ring
    _ = hint * ((iSup f)⁻¹^(1-θ) * (iSup g)⁻¹^θ) := by rw [lintegral_mul_const]; exact hh_measurable
    _ = hint * (iSup f)⁻¹^(1-θ) * (iSup g)⁻¹^θ := by ring

  change factor * fint^(1-θ) * gint^θ ≤ hint
  calc
    factor * fint^(1-θ) * gint^θ = factor * (f'int * iSup f)^(1-θ) * (g'int * iSup g)^θ := by
      rw [f'int_to_fint, g'int_to_gint]
      congr
      · exact (ENNReal.inv_mul_cancel_right iSupf_ne_zero hf_bounded).symm
      exact (ENNReal.inv_mul_cancel_right iSupg_ne_zero hg_bounded).symm
    _ = (factor * f'int^(1-θ) * g'int^θ) * ((iSup f)^(1-θ) * (iSup g)^θ) := by
      rw [ENNReal.mul_rpow_of_nonneg, ENNReal.mul_rpow_of_nonneg]
      · ring
      · linarith
      linarith
    _ ≤ h'int * ((iSup f)^(1-θ) * (iSup g)^θ) := by
      rw [ENNReal.mul_le_mul_iff_left]
      · exact normalized_result
      · rw [← pos_iff_ne_zero]; exact ENNReal.mul_pos iSupf_pow_ne_zero iSupg_pow_ne_zero
      · exact ENNReal.mul_ne_top iSupf_pow_ne_top iSupg_pow_ne_top
    _ = (hint * (iSup f)⁻¹^(1-θ) * (iSup g)⁻¹^θ) * ((iSup f)^(1-θ) * (iSup g)^θ) := by
      rw [h'int_to_hint]
    _ = hint * ((iSup f)⁻¹^(1-θ) * (iSup f)^(1-θ)) * ((iSup g)⁻¹^θ * (iSup g)^θ) := by ring
    _ = hint * (((iSup f)^(1-θ))⁻¹ * (iSup f)^(1-θ)) * (((iSup g)^θ)⁻¹ * (iSup g)^θ) := by
      congr
      · rw [ENNReal.inv_rpow]
      rw [ENNReal.inv_rpow]
    _ = hint * 1 * 1 := by
      congr
      · exact ENNReal.inv_mul_cancel iSupf_pow_ne_zero iSupf_pow_ne_top
      exact ENNReal.inv_mul_cancel iSupg_pow_ne_zero iSupg_pow_ne_top
    _ = hint := by ring
end GaussianPerimeter.VolumeComparison
