-- Prove2me | solution 1 for DistanceGeometry.centeredGram_apply_eq_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:46:07.546107+00:00
-- url     : https://prove2.me/submissions/6abf6808-669b-4806-8c52-db823bf4a592

module
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Algebra.Order.Star.Real
public import Definitions.Def_LeanPool_DistanceGeometry_Schoenberg
public import Theorems.Thm_DistanceGeometry_centeredGram_apply
attribute [local simp] DistanceGeometry.centeredGram_apply



set_option autoImplicit true
@[expose] public section
public section
open DistanceGeometry
open Matrix
open scoped RealInnerProductSpace
variable {n k : ℕ} [NeZero n]
namespace DistanceGeometry
theorem _root_.solution
    {D : Matrix (Fin n) (Fin n) ℝ} {x : Fin n → EuclideanSpace ℝ (Fin k)}
    (hD : IsSqDistMatrix D x) (i j : Fin n) :
    centeredGram D i j = ⟪x i - x 0, x j - x 0⟫ := by
  have key := real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two
    (x i - x 0) (x j - x 0)
  -- unfold the basepoint-centered Gram entry and replace each `D` entry by its squared distance
  rw [centeredGram_apply, hD 0 i, hD 0 j, hD i j, key]
  -- turn distances into norms
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
  -- `‖x 0 - x i‖ = ‖x i - x 0‖`, etc.; `(x i - x 0) - (x j - x 0) = x i - x j`
  rw [norm_sub_rev (x 0) (x i), norm_sub_rev (x 0) (x j)]
  have hsub : (x i - x 0) - (x j - x 0) = x i - x j := by abel
  rw [hsub, pow_two, pow_two, pow_two]
end DistanceGeometry
