-- Prove2me | solution 1 for Finset.affineDim_add_one_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:07:09.877315+00:00
-- url     : https://prove2.me/submissions/0af91a44-b58b-4ea2-9994-43c8deb9c10d

module
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Theorems.Thm_Finset_affineDim_eq_finrank_vectorSpan
public import Theorems.Thm_Finset_affineDim_empty
public import Theorems.Thm_Finset_affineDim_singleton
public import Theorems.Thm_Finset_affineDim_vadd_finset
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
theorem _root_.solution {S : Finset (Fin D → ℝ)} (hS : S.Nonempty) :
    S.affineDim + 1 ≤ #S := by
  have : Nonempty (S : Set (Fin D → ℝ)) := hS.to_set.to_subtype
  have h := finrank_vectorSpan_range_add_one_le ℝ ((↑) : ↥(S : Set (Fin D → ℝ)) → Fin D → ℝ)
  rw [Subtype.range_coe, ← affineDim_eq_finrank_vectorSpan] at h
  simpa using h
end Finset
