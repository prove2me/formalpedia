-- Prove2me | solution 1 for GaussianPerimeter.isometry_facetEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T12:18:08.659501+00:00
-- url     : https://prove2.me/submissions/cac9178a-77fb-48c0-9713-b0fe16f33fdd

module
public import Definitions.Def_GaussianPerimeter_Definitions
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Definitions.Def_GaussianPerimeter_Geometry

set_option autoImplicit true
@[expose] public section
public section
open Function Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal InnerProductSpace RealInnerProductSpace Function
open GaussianPerimeter
local notation "Euc" k => EuclideanSpace ℝ (Fin k)
namespace GaussianPerimeter
theorem _root_.solution {k : ℕ} (u : Euc (k + 1)) (hu : ‖u‖ = 1)
    (ρ : ℝ) : Isometry (facetEmbedding u hu ρ) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [facetEmbedding, facetEmbedding, dist_add_left]
  rw [facetTangent, facetTangent, (normalReflection u).isometry.dist_eq]
  exact (facetBasis (referenceNormal k) (norm_referenceNormal k)).repr.symm.isometry.dist_eq _ _
end GaussianPerimeter
