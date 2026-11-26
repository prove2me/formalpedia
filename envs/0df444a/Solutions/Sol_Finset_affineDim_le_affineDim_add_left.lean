-- Prove2me | solution 1 for Finset.affineDim_le_affineDim_add_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:10:44.433253+00:00
-- url     : https://prove2.me/submissions/984b91e9-5d94-4068-b578-54c78293901d

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDimSumset
public import Theorems.Thm_Finset_affineDim_le_affineDim_add_right

set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
variable {D : ℕ}
namespace Finset
theorem _root_.solution {A : Finset (Fin D → ℝ)} (hA : A.Nonempty)
    (B : Finset (Fin D → ℝ)) : B.affineDim ≤ (A + B).affineDim := by
  rw [add_comm]
  exact affineDim_le_affineDim_add_right B hA
end Finset
