-- Prove2me | solution 1 for DistanceGeometry.rank_centeredGram_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:47:41.896591+00:00
-- url     : https://prove2.me/submissions/27525bf7-c45d-498b-bb0f-9f27dd21e66b

module
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Algebra.Order.Star.Real
public import Definitions.Def_LeanPool_DistanceGeometry_Schoenberg
public import Theorems.Thm_DistanceGeometry_centeredGram_eq_gram

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
    (hD : IsSqDistMatrix D x) :
    (centeredGram D).rank ≤ k := by
  rw [centeredGram_eq_gram hD]
  -- factor the Gram matrix as `mᴴ * m` over the standard orthonormal basis
  set b : OrthonormalBasis (Fin k) ℝ (EuclideanSpace ℝ (Fin k)) :=
    EuclideanSpace.basisFun (Fin k) ℝ with hb
  rw [gram_eq_conjTranspose_mul b (fun i => x i - x 0)]
  set m : Matrix (Fin k) (Fin n) ℝ := of fun i j => b.repr ((fun i => x i - x 0) j) i with hm
  rw [rank_conjTranspose_mul_self m]
  calc m.rank ≤ Fintype.card (Fin k) := rank_le_card_height m
    _ = k := Fintype.card_fin k
end DistanceGeometry
