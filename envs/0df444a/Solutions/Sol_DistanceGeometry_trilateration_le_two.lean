-- Prove2me | solution 1 for DistanceGeometry.trilateration_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:46:53.210245+00:00
-- url     : https://prove2.me/submissions/3004974f-1f21-43fa-85e9-ee0ead0813b1

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Basic
public import Definitions.Def_LeanPool_DistanceGeometry_Trilateration
public import Theorems.Thm_DistanceGeometry_mem_sphereIntersection
public import Theorems.Thm_DistanceGeometry_encard_setOf_forall_dist_eq_le_two
attribute [local simp] DistanceGeometry.mem_sphereIntersection

set_option autoImplicit true
@[expose] public section
public section
open DistanceGeometry
open scoped RealInnerProductSpace
open EuclideanGeometry Module Submodule
variable {c : Fin 3 → EuclideanSpace ℝ (Fin 3)}
namespace DistanceGeometry
theorem _root_.solution (hc : AffineIndependent ℝ c) (r : Fin 3 → ℝ) :
    (trilaterationSet c r).encard ≤ 2 := by
  -- the centers span a plane, so the orthogonal complement is a line
  have hW : Module.finrank ℝ (vectorSpan ℝ (Set.range c)) = 2 := hc.finrank_vectorSpan (by simp)
  have h3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hperp : Module.finrank ℝ (vectorSpan ℝ (Set.range c))ᗮ = 1 := by
    have hsum := Submodule.finrank_add_finrank_orthogonal
      (K := vectorSpan ℝ (Set.range c))
    rw [hW, h3] at hsum
    omega
  exact encard_setOf_forall_dist_eq_le_two hperp r
end DistanceGeometry
