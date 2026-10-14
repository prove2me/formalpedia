-- Prove2me | solution 1 for DbarRegularity.eLpNorm_integral_mul_sub_le_of_hormander_of_lt_two
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T16:51:43.728785+00:00
-- url     : https://prove2.me/submissions/98edf20e-10fa-4a46-858e-d18a8b737405

import Definitions.Def_DbarRegularity_Setting
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Theorems.Thm_DbarRegularity_weakType_one_integral_mul_sub_of_hormander
import Theorems.Thm_DbarRegularity_marcinkiewicz_interpolation
import Theorems.Thm_DbarRegularity_ae_integrable_mul_sub_of_memLp_two_of_integrable
import Theorems.Thm_DbarRegularity_integrable_mul_sub_of_memLp_two
import Theorems.Thm_DbarRegularity_aestronglyMeasurable_integral_mul_sub
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov



namespace DbarRegularity

open MeasureTheory Set
open scoped ENNReal NNReal

/-- `L^p` bound, `1 < p < 2`, for convolution with an `L²` kernel `K` on `ℝ^d` that satisfies the
Hörmander condition with constant `B₁` and is bounded on `L²` with norm `B₂`; the constant
depends only on `d`, `p`, `B₁`, `B₂`. -/
theorem eLpNorm_integral_mul_sub_le_of_hormander_of_lt_two {d : ℕ} (hd : 0 < d) (p : ℝ≥0∞)
    (hp : 1 < p) (hp2 : p < 2) (B₁ B₂ : ℝ≥0) :
    ∃ A : ℝ≥0, ∀ K : EuclideanSpace ℝ (Fin d) → ℂ, MemLp K 2 volume →
      (∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ B₁) →
      (∀ g, MemLp g 2 volume →
        eLpNorm (fun x => ∫ y, K (x - y) * g y) 2 volume ≤ B₂ * eLpNorm g 2 volume) →
      ∀ f, MemLp f p volume →
        eLpNorm (fun x => ∫ y, K (x - y) * f y) p volume ≤ A * eLpNorm f p volume := by
  obtain ⟨C, hC⟩ := weakType_one_integral_mul_sub_of_hormander hd
  obtain ⟨A, hA⟩ := marcinkiewicz_interpolation 2 p (by norm_num) hp hp2
    (C * (1 + B₁ + B₂ ^ 2)) B₂
  refine ⟨A, fun K hK hH hL2 f hf => ?_⟩
  have hint : ∀ f : EuclideanSpace ℝ (Fin d) → ℂ,
      (∃ f₁ f₂, MemLp f₁ 1 volume ∧ MemLp f₂ 2 volume ∧ f = f₁ + f₂) →
      ∀ᵐ x, Integrable (fun y => K (x - y) * f y) volume := by
    rintro f ⟨f₁, f₂, h1, h2, rfl⟩
    filter_upwards [ae_integrable_mul_sub_of_memLp_two_of_integrable hK
      (memLp_one_iff_integrable.1 h1)] with x hx
    refine (hx.add (integrable_mul_sub_of_memLp_two hK h2 x)).congr
      (ae_of_all _ fun y => ?_)
    simp only [Pi.add_apply]; ring
  refine hA d (fun f x => ∫ y, K (x - y) * f y) ?_ ?_
    (fun f hf α hα => hC K hK B₁ B₂ hH hL2 f hf α hα) ?_ (fun h => absurd h (by norm_num)) f hf
  · rintro f ⟨f₁, f₂, h1, h2, rfl⟩
    exact aestronglyMeasurable_integral_mul_sub K _ hK.1 (h1.1.add h2.1)
  · intro f g hf hg
    filter_upwards [hint f hf, hint g hg] with x h1 h2
    simp only [Pi.add_apply, mul_add]
    rw [integral_add h1 h2]
    exact norm_add_le _ _
  · intro _ f hf α hα
    have hα0 : (α : ℝ≥0∞) ≠ 0 := by simpa using hα.ne'
    have cheb := meas_ge_le_mul_pow_eLpNorm_enorm volume (p := (2 : ℝ≥0∞)) (by norm_num)
      (by norm_num) (aestronglyMeasurable_integral_mul_sub K f hK.1 hf.1) hα0
      (fun h => absurd h ENNReal.coe_ne_top)
    simp only [ENNReal.toReal_ofNat] at cheb ⊢
    calc volume {x | (α : ℝ≥0∞) < ‖∫ y, K (x - y) * f y‖ₑ}
        ≤ volume {x | (α : ℝ≥0∞) ≤ ‖∫ y, K (x - y) * f y‖ₑ} :=
          measure_mono (setOf_subset_setOf.2 fun x hx => le_of_lt hx)
      _ ≤ (α : ℝ≥0∞)⁻¹ ^ (2 : ℝ) *
            eLpNorm (fun x => ∫ y, K (x - y) * f y) 2 volume ^ (2 : ℝ) := cheb
      _ ≤ (α : ℝ≥0∞)⁻¹ ^ (2 : ℝ) * ((B₂ : ℝ≥0∞) * eLpNorm f 2 volume) ^ (2 : ℝ) := by
          gcongr; exact hL2 f hf
      _ = ((B₂ : ℝ≥0∞) / α * eLpNorm f 2 volume) ^ (2 : ℝ) := by
          rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
          congr 1; rw [div_eq_mul_inv]; ring

end DbarRegularity

open DbarRegularity

open MeasureTheory Set
open scoped ENNReal NNReal

theorem solution {d : ℕ} (hd : 0 < d) (p : ℝ≥0∞)
    (hp : 1 < p) (hp2 : p < 2) (B₁ B₂ : ℝ≥0) :
    ∃ A : ℝ≥0, ∀ K : EuclideanSpace ℝ (Fin d) → ℂ, MemLp K 2 volume →
      (∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ B₁) →
      (∀ g, MemLp g 2 volume →
        eLpNorm (fun x => ∫ y, K (x - y) * g y) 2 volume ≤ B₂ * eLpNorm g 2 volume) →
      ∀ f, MemLp f p volume →
        eLpNorm (fun x => ∫ y, K (x - y) * f y) p volume ≤ A * eLpNorm f p volume :=
  eLpNorm_integral_mul_sub_le_of_hormander_of_lt_two hd p hp hp2 B₁ B₂
