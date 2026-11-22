-- Prove2me | solution 1 for DistanceGeometry.posSemidef_centeredGram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:47:41.444436+00:00
-- url     : https://prove2.me/submissions/b3b6a4ec-92c2-4099-b4df-40d84f8f8ad7

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
    (centeredGram D).PosSemidef := by
  rw [centeredGram_eq_gram hD]
  exact posSemidef_gram ℝ _
end DistanceGeometry
