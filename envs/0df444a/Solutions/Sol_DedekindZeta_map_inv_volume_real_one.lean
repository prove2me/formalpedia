-- Prove2me | solution 1 for DedekindZeta.map_inv_volume_real_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:28:22.873957+00:00
-- url     : https://prove2.me/submissions/dc8a2042-fdb0-4a5f-a58a-a23ea1a7a192

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply



set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
open DedekindZeta
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
variable {K : Type*} [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta
theorem _root_.solution :
    Measure.map (fun t : ℝ => t⁻¹) volume
      = volume.withDensity (fun t : ℝ => ENNReal.ofReal (‖t‖ ^ 2)⁻¹) := by
  -- Density measurability.
  have hdens : Measurable (fun t : ℝ => ENNReal.ofReal (‖t‖ ^ 2)⁻¹) :=
    ((measurable_norm.pow_const 2).inv).ennreal_ofReal
  -- We test both measures against an arbitrary measurable `g`.
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  rw [lintegral_map hg measurable_inv,
    lintegral_withDensity_eq_lintegral_mul volume hdens hg]
  simp only [Pi.mul_apply]
  -- Now: `∫⁻ a, g a⁻¹ = ∫⁻ a, ofReal (‖a‖²)⁻¹ * g a`.
  -- Splitting principle: the fixed point `0` is volume-null.
  have hdisj : Disjoint (Set.Iio (0 : ℝ)) (Set.Ioi 0) := by
    rw [Set.disjoint_left]; intro x hx hx'
    exact absurd ((Set.mem_Ioi.1 hx').trans (Set.mem_Iio.1 hx)) (lt_irrefl 0)
  have hset : Set.Iio (0 : ℝ) ∪ Set.Ioi 0 = ({(0 : ℝ)}ᶜ) := by
    ext x
    simp only [Set.mem_union, Set.mem_Iio, Set.mem_Ioi, Set.mem_compl_iff,
      Set.mem_singleton_iff, lt_or_lt_iff_ne, ne_eq]
  have hae : ((Set.Iio (0 : ℝ) ∪ Set.Ioi (0 : ℝ) : Set ℝ)) =ᵐ[volume] (Set.univ : Set ℝ) := by
    rw [hset]; exact ae_eq_univ.2 (by simp)
  have split : ∀ F : ℝ → ℝ≥0∞,
      ∫⁻ x, F x ∂volume = (∫⁻ x in Set.Iio (0 : ℝ), F x) + ∫⁻ x in Set.Ioi (0 : ℝ), F x := by
    intro F
    rw [← setLIntegral_univ F, ← setLIntegral_congr hae,
      lintegral_union measurableSet_Ioi hdisj]
  -- The pointwise identity `|f' x| · ofReal (‖x⁻¹‖²)⁻¹ = 1` for `x ≠ 0`.
  have hscalar : ∀ x : ℝ, x ≠ 0 →
      ENNReal.ofReal |(-(x ^ 2)⁻¹)| * (ENNReal.ofReal (‖x⁻¹‖ ^ 2)⁻¹ * g x⁻¹) = g x⁻¹ := by
    intro x hx
    have hx2 : (0 : ℝ) < x ^ 2 := by positivity
    rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (x ^ 2)⁻¹),
      show ‖x⁻¹‖ ^ 2 = (x ^ 2)⁻¹ from by rw [Real.norm_eq_abs, sq_abs, inv_pow], inv_inv,
      ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
      inv_mul_cancel₀ (ne_of_gt hx2), ENNReal.ofReal_one, one_mul]
  -- Change of variables on `(0, ∞)`: `t ↦ t⁻¹` is an antitone diffeomorphism
  -- with derivative `-(x²)⁻¹`, mapping `Set.Ioi 0` onto itself.
  have key_pos : (∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (‖x‖ ^ 2)⁻¹ * g x)
      = ∫⁻ x in Set.Ioi (0 : ℝ), g x⁻¹ := by
    have himg : (fun t : ℝ => t⁻¹) '' Set.Ioi (0 : ℝ) = Set.Ioi 0 := by
      ext y; simp only [Set.mem_image, Set.mem_Ioi]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact inv_pos.2 hx
      · intro hy; exact ⟨y⁻¹, inv_pos.2 hy, inv_inv y⟩
    have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
        HasDerivWithinAt (fun t : ℝ => t⁻¹) (-(x ^ 2)⁻¹) (Set.Ioi 0) x :=
      fun x hx => (hasDerivAt_inv (ne_of_gt hx)).hasDerivWithinAt
    have hcov := lintegral_image_eq_lintegral_abs_deriv_mul (f := fun t : ℝ => t⁻¹)
      (f' := fun x => -(x ^ 2)⁻¹) measurableSet_Ioi hderiv inv_injective.injOn
      (fun y => ENNReal.ofReal (‖y‖ ^ 2)⁻¹ * g y)
    rw [himg] at hcov
    rw [hcov]
    exact setLIntegral_congr_fun measurableSet_Ioi fun x hx => hscalar x (ne_of_gt hx)
  -- Change of variables on `(-∞, 0)`.
  have key_neg : (∫⁻ x in Set.Iio (0 : ℝ), ENNReal.ofReal (‖x‖ ^ 2)⁻¹ * g x)
      = ∫⁻ x in Set.Iio (0 : ℝ), g x⁻¹ := by
    have himg : (fun t : ℝ => t⁻¹) '' Set.Iio (0 : ℝ) = Set.Iio 0 := by
      ext y; simp only [Set.mem_image, Set.mem_Iio]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact inv_lt_zero.2 hx
      · intro hy; exact ⟨y⁻¹, inv_lt_zero.2 hy, inv_inv y⟩
    have hderiv : ∀ x ∈ Set.Iio (0 : ℝ),
        HasDerivWithinAt (fun t : ℝ => t⁻¹) (-(x ^ 2)⁻¹) (Set.Iio 0) x :=
      fun x hx => (hasDerivAt_inv (ne_of_lt hx)).hasDerivWithinAt
    have hcov := lintegral_image_eq_lintegral_abs_deriv_mul (f := fun t : ℝ => t⁻¹)
      (f' := fun x => -(x ^ 2)⁻¹) measurableSet_Iio hderiv inv_injective.injOn
      (fun y => ENNReal.ofReal (‖y‖ ^ 2)⁻¹ * g y)
    rw [himg] at hcov
    rw [hcov]
    exact setLIntegral_congr_fun measurableSet_Iio fun x hx => hscalar x (ne_of_lt hx)
  rw [split (fun a => g a⁻¹), split (fun a => ENNReal.ofReal (‖a‖ ^ 2)⁻¹ * g a),
    key_pos, key_neg]
end DedekindZeta
