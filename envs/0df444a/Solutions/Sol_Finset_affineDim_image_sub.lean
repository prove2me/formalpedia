-- Prove2me | solution 1 for Finset.affineDim_image_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:09:33.521107+00:00
-- url     : https://prove2.me/submissions/ed3fb1b7-fae8-4736-a5c8-1e284c081871

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
public import Theorems.Thm_Finset_affineDim_image_add_right
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
theorem _root_.solution (S : Finset (Fin D → ℝ)) (c : Fin D → ℝ) :
    (S.image fun x ↦ x - c).affineDim = S.affineDim := by
  simp only [sub_eq_add_neg, affineDim_image_add_right]
end Finset
