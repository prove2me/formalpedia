-- Prove2me | solution 1 for GaussianPerimeter.inner_facetEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:05:49.350798+00:00
-- url     : https://prove2.me/submissions/a224e98b-8b97-4811-9a74-fe0d9be1c7ca

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
    (ρ : ℝ) (y : Euc k) : ⟪u, facetEmbedding u hu ρ y⟫_ℝ = ρ := by
  simp [facetEmbedding, inner_add_right, inner_facetTangent u hu y, real_inner_smul_right,
    hu]
end GaussianPerimeter
