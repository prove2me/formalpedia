-- Prove2me | solution 1 for GaussianPerimeter.norm_sq_facetEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:10:38.890799+00:00
-- url     : https://prove2.me/submissions/8f8358d6-7f8f-4fc3-a2cb-6ee4783b4850

module
public import Definitions.Def_GaussianPerimeter_Definitions
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Definitions.Def_GaussianPerimeter_Geometry
section
public section
open Function Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal InnerProductSpace RealInnerProductSpace Function
namespace GaussianPerimeter
local notation "Euc" k => EuclideanSpace ℝ (Fin k)
private theorem normalReflection_apply_referenceNormal {k : ℕ} (u : Euc (k + 1))
    (hu : ‖u‖ = 1) : normalReflection u (referenceNormal k) = u :=
  Submodule.reflection_sub ((norm_referenceNormal k).trans hu.symm)
private theorem inner_facetTangent {k : ℕ} (u : Euc (k + 1)) (hu : ‖u‖ = 1)
    (y : Euc k) : ⟪u, facetTangent u y⟫_ℝ = 0 := by
  calc
    ⟪u, facetTangent u y⟫_ℝ =
        ⟪normalReflection u (referenceNormal k), normalReflection u (referenceTangent y)⟫_ℝ := by
      rw [normalReflection_apply_referenceNormal u hu, facetTangent]
    _ = ⟪referenceNormal k, (referenceTangent y : Euc (k + 1))⟫_ℝ :=
      (normalReflection u).inner_map_map _ _
    _ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp (referenceTangent y).2
variable {k : ℕ} {ι : Type*}
end GaussianPerimeter
end
end

set_option autoImplicit true
@[expose] public section
public section
open Function Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal InnerProductSpace RealInnerProductSpace Function
open GaussianPerimeter
local notation "Euc" k => EuclideanSpace ℝ (Fin k)
namespace GaussianPerimeter
theorem _root_.solution {k : ℕ} (u : Euc (k + 1)) (hu : ‖u‖ = 1)
    (ρ : ℝ) (y : Euc k) : ‖facetEmbedding u hu ρ y‖ ^ 2 = ρ ^ 2 + ‖y‖ ^ 2 := by
  have horth : ⟪ρ • u, facetTangent u y⟫_ℝ = 0 := by
    simp [real_inner_smul_left, inner_facetTangent u hu y]
  have hnorm : ‖facetTangent u y‖ = ‖y‖ := by
    rw [facetTangent, (normalReflection u).norm_map]
    exact (facetBasis (referenceNormal k) (norm_referenceNormal k)).repr.symm.norm_map y
  calc
    ‖facetEmbedding u hu ρ y‖ ^ 2 = ‖ρ • u‖ ^ 2 + ‖facetTangent u y‖ ^ 2 := by
      simpa only [facetEmbedding, pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real horth
    _ = ρ ^ 2 + ‖y‖ ^ 2 := by rw [norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs, hnorm]
end GaussianPerimeter
