-- Prove2me | solution 1 for Finset.affineDim_image_add_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:08:56.784807+00:00
-- url     : https://prove2.me/submissions/cd2bcfa1-abd3-483a-8eb4-469ece0ae238

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
public import Theorems.Thm_Finset_affineDim_image_add_left
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
theorem _root_.solution (c : Fin D → ℝ) (S : Finset (Fin D → ℝ)) :
    (S.image (· + c)).affineDim = S.affineDim := by
  simp only [add_comm _ c, affineDim_image_add_left]
end Finset
