-- Prove2me | solution 1 for DistanceGeometry.schoenberg_easy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:48:26.668818+00:00
-- url     : https://prove2.me/submissions/0e1e2dcd-f2b6-4271-a475-eadca99c68a1

module
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Algebra.Order.Star.Real
public import Definitions.Def_LeanPool_DistanceGeometry_Schoenberg
public import Theorems.Thm_DistanceGeometry_posSemidef_centeredGram
public import Theorems.Thm_DistanceGeometry_rank_centeredGram_le

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
    (centeredGram D).PosSemidef ∧ (centeredGram D).rank ≤ k :=
  ⟨posSemidef_centeredGram hD, rank_centeredGram_le hD⟩
end DistanceGeometry
