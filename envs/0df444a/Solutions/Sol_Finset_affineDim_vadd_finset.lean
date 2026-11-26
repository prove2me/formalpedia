-- Prove2me | solution 1 for Finset.affineDim_vadd_finset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:06.91215+00:00
-- url     : https://prove2.me/submissions/b23ba903-d393-469b-8b75-0de4a13ad8d3

module
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Theorems.Thm_Finset_affineDim_eq_finrank_vectorSpan

set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
variable {D : ℕ}
namespace Finset
theorem _root_.solution (c : Fin D → ℝ) (S : Finset (Fin D → ℝ)) :
    (c +ᵥ S).affineDim = S.affineDim := by
  rw [affineDim_eq_finrank_vectorSpan, coe_vadd_finset, vectorSpan_vadd,
    affineDim_eq_finrank_vectorSpan]
end Finset
