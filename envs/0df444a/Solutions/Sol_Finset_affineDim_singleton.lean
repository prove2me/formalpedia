-- Prove2me | solution 1 for Finset.affineDim_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:30.522901+00:00
-- url     : https://prove2.me/submissions/b1be8622-f538-4c17-9f76-2f33d7863c41

module
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Theorems.Thm_Finset_affineDim_eq_finrank_vectorSpan
public import Theorems.Thm_Finset_affineDim_empty
attribute [local simp] Finset.affineDim_empty

set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
variable {D : ℕ}
namespace Finset
theorem _root_.solution (x : Fin D → ℝ) : ({x} : Finset (Fin D → ℝ)).affineDim = 0 := by
  simp [affineDim_eq_finrank_vectorSpan]
end Finset
