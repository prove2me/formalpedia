-- Prove2me | solution 1 for Finset.affineDim_eq_finrank_span_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:08.159019+00:00
-- url     : https://prove2.me/submissions/3596f3a0-0603-4a8c-b680-23494f08e6e9

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
theorem _root_.solution (S : Finset (Fin D → ℝ)) :
    S.affineDim = Module.finrank ℝ (Submodule.span ℝ (↑S - ↑S : Set (Fin D → ℝ))) := by
  rw [affineDim_eq_finrank_vectorSpan, vectorSpan_def]
  rfl
end Finset
