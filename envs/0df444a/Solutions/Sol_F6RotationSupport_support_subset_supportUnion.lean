-- Prove2me | solution 1 for F6RotationSupport.support_subset_supportUnion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:06:58.002365+00:00
-- url     : https://prove2.me/submissions/1b8ba259-bfd2-4600-a886-3b0ffe270fdf

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
import Theorems.Thm_F6RotationSupport_mem_supportUnion
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_mem_part
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_antichains
import Theorems.Thm_F6ConvexWindow_mem_ideal
attribute [local simp] F6ConvexWindow.ChainDecomposition.mem_part
attribute [local simp] F6ConvexWindow.mem_Inc
attribute [local simp] F6ConvexWindow.mem_antichains
attribute [local simp] F6ConvexWindow.mem_ideal


attribute [local simp] F6RotationSupport.mem_supportUnion

set_option autoImplicit true
noncomputable section
open F6RotationSupport
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]
namespace F6RotationSupport
theorem _root_.solution (supp : R → Finset M) {Q : Finset R}
    {rho : R} (hrho : rho ∈ Q) : supp rho ⊆ supportUnion supp Q := by
  intro m hm
  exact mem_supportUnion.mpr ⟨rho, hrho, hm⟩
end F6RotationSupport
