-- Prove2me | solution 1 for Finset.affineDim_image_add_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:08:29.60981+00:00
-- url     : https://prove2.me/submissions/292237cd-68a5-4392-9585-383b53aadaf4

module
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Theorems.Thm_Finset_affineDim_vadd_finset
attribute [local simp] Finset.affineDim_vadd_finset

set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
variable {D : ℕ}
namespace Finset
theorem _root_.solution (c : Fin D → ℝ) (S : Finset (Fin D → ℝ)) :
    (S.image (c + ·)).affineDim = S.affineDim :=
  affineDim_vadd_finset c S
end Finset
