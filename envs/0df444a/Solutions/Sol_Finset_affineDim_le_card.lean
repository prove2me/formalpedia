-- Prove2me | solution 1 for Finset.affineDim_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:10:43.900448+00:00
-- url     : https://prove2.me/submissions/e3c0aec9-2cd4-48af-a3dd-a4214d807831

module
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Theorems.Thm_Finset_affineDim_empty
public import Theorems.Thm_Finset_affineDim_singleton
public import Theorems.Thm_Finset_affineDim_vadd_finset
public import Theorems.Thm_Finset_affineDim_add_one_le_card
attribute [local simp] Finset.affineDim_empty
attribute [local simp] Finset.affineDim_singleton
attribute [local simp] Finset.affineDim_vadd_finset

set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
variable {D : ℕ}
namespace Finset
theorem _root_.solution (S : Finset (Fin D → ℝ)) : S.affineDim ≤ #S := by
  obtain rfl | hS := S.eq_empty_or_nonempty
  · simp
  · grind [affineDim_add_one_le_card hS]
end Finset
