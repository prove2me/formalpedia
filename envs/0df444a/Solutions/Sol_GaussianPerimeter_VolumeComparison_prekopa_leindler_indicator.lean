-- Prove2me | solution 1 for GaussianPerimeter.VolumeComparison.prekopa_leindler_indicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:29:55.420768+00:00
-- url     : https://prove2.me/submissions/09580137-9434-49c7-b18a-f4d3b57cf5f0

module
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Definitions.Def_GaussianPerimeter_PrekopaLeindler
public import Definitions.Def_GaussianPerimeter_BrunnMinkowski
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_prekopa_leindler


set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter GaussianPerimeter.VolumeComparison
open MeasureTheory Set
open scoped Pointwise
namespace GaussianPerimeter.VolumeComparison
theorem _root_.solution
    {d : ℕ} {θ : ℝ} {A B : Set (Fin (d + 1) → ℝ)}
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hA_measurable : MeasurableSet A) (hB_measurable : MeasurableSet B)
    (hAB_measurable : MeasurableSet (A + B))
    : ENNReal.ofReal ((1-θ)^((d+1)*(1-θ))*θ^((d+1)*θ))⁻¹
      * volume A^(1-θ) * volume B^θ ≤ volume (A + B) := by
  have : ENNReal.ofReal ((1-θ)^((d+1)*(1-θ))*θ^((d+1)*θ))⁻¹
      * (∫⁻ x, (A.indicator fun _ ↦ (1 : ENNReal)) x)^(1-θ)
      * (∫⁻ x, (B.indicator fun _ ↦ (1 : ENNReal)) x)^θ
      ≤ ∫⁻ x, ((A + B).indicator fun _ ↦ (1 : ENNReal)) x := prekopa_leindler ⟨
    hθ0, hθ1, by measurability, by measurability, by measurability, by
    show ∀ (x y : Fin (d + 1) → ℝ),
      ((A.indicator fun _ ↦ (1 : ENNReal)) x) ^ (1 - θ)
      * ((B.indicator fun _ ↦ (1 : ENNReal)) y) ^ θ
      ≤ ((A + B).indicator fun _ ↦ (1 : ENNReal)) (x + y)
    intro x y
    unfold indicator
    simp_all only [ite_pow, ENNReal.one_rpow, sub_pos, ENNReal.zero_rpow_of_pos, mul_ite, mul_one,
      mul_zero]
    split
    · split
      · split
        · rfl
        · expose_names; exact False.elim (h_2 (add_mem_add h_1 h))
      · simp only [zero_le]
    simp only [zero_le]⟩
  simp_all
end GaussianPerimeter.VolumeComparison
