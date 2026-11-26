-- Prove2me | solution 1 for Finset.affineDim_eq_finrank_vectorSpan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:32.869814+00:00
-- url     : https://prove2.me/submissions/195d35c1-4f12-47b6-8cd4-9b3aee8f8f95

module
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim

set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
variable {D : ℕ}
namespace Finset
theorem _root_.solution (S : Finset (Fin D → ℝ)) :
    S.affineDim = Module.finrank ℝ (vectorSpan ℝ (S : Set (Fin D → ℝ))) := by
  rw [affineDim, direction_affineSpan]
end Finset
