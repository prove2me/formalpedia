-- Prove2me | solution 1 for Finset.affineDim_le_affineDim_add_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:09:32.9738+00:00
-- url     : https://prove2.me/submissions/86031846-8b28-4e93-b1cb-bc765a763a29

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDimSumset
public import Theorems.Thm_Finset_affineDim_image_add_right
public import Theorems.Thm_Finset_affineDim_mono


set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
variable {D : ℕ}
namespace Finset
theorem _root_.solution (A : Finset (Fin D → ℝ))
    {B : Finset (Fin D → ℝ)} (hB : B.Nonempty) : A.affineDim ≤ (A + B).affineDim := by
  obtain ⟨b, hb⟩ := hB
  rw [← affineDim_image_add_right b A]
  apply affineDim_mono
  rw [image_subset_iff]
  intro a ha
  exact add_mem_add ha hb
end Finset
