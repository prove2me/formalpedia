-- Prove2me | solution 1 for Finset.affineDim_add_eq_of_left_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:10:12.02191+00:00
-- url     : https://prove2.me/submissions/eaf4491c-2adb-4b02-bcb0-63edc424975c

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDimSumset
public import Theorems.Thm_Finset_affineDim_le_affineDim_add_right
public import Theorems.Thm_Finset_affineDim_le


set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
variable {D : ℕ}
namespace Finset
theorem _root_.solution {A B : Finset (Fin D → ℝ)} (hB : B.Nonempty)
    (hA : A.affineDim = D) : (A + B).affineDim = D :=
  le_antisymm (affineDim_le _)
    (hA.symm.trans_le (affineDim_le_affineDim_add_right A hB))
end Finset
