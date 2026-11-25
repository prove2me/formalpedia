-- Prove2me | solution 1 for F6RotationSupport.mem_commonInc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:51:03.709996+00:00
-- url     : https://prove2.me/submissions/1c1dc45f-bf1d-4117-b65c-cc2fcec837db

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
import Theorems.Thm_F6RotationSupport_mem_supportUnion
import Theorems.Thm_F6RotationSupport_mem_interval
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_mem_part
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_antichains
import Theorems.Thm_F6ConvexWindow_mem_ideal
attribute [local simp] F6ConvexWindow.ChainDecomposition.mem_part
attribute [local simp] F6ConvexWindow.mem_Inc
attribute [local simp] F6ConvexWindow.mem_antichains
attribute [local simp] F6ConvexWindow.mem_ideal


attribute [local simp] F6RotationSupport.mem_supportUnion
attribute [local simp] F6RotationSupport.mem_interval

set_option autoImplicit true
noncomputable section
open F6RotationSupport
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]
namespace F6RotationSupport
theorem _root_.solution {alpha beta rho : R} :
    rho ∈ commonInc alpha beta ↔
      F6ConvexWindow.IncRel alpha rho ∧ F6ConvexWindow.IncRel beta rho := by
  simp [commonInc]
end F6RotationSupport
