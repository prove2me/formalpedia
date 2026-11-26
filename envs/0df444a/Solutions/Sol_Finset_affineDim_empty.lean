-- Prove2me | solution 1 for Finset.affineDim_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:01.84739+00:00
-- url     : https://prove2.me/submissions/fc36d1cf-5b09-4c41-a1de-e777ee6f15da

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
theorem _root_.solution : (∅ : Finset (Fin D → ℝ)).affineDim = 0 := by
  simp [affineDim_eq_finrank_vectorSpan]
end Finset
