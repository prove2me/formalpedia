-- Prove2me | solution 1 for DistanceGeometry.centeredGram_eq_gram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:46:54.932745+00:00
-- url     : https://prove2.me/submissions/3a5661a2-31c1-47c2-bb62-027a743a6b82

module
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Algebra.Order.Star.Real
public import Definitions.Def_LeanPool_DistanceGeometry_Schoenberg
public import Theorems.Thm_DistanceGeometry_centeredGram_apply_eq_inner

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
    centeredGram D = gram ℝ (fun i => x i - x 0) := by
  ext i j
  rw [centeredGram_apply_eq_inner hD i j, gram_apply]
end DistanceGeometry
