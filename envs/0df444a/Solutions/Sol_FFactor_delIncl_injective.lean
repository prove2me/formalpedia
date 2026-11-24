-- Prove2me | solution 1 for FFactor.delIncl_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:53:25.673703+00:00
-- url     : https://prove2.me/submissions/34ea02ef-28fe-4bbf-ba87-875980720b4c

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
public import Theorems.Thm_FFactor_mem_del_verts
attribute [local simp] FFactor.mem_del_verts

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open FFactor
variable {W : Type*} (Γ : SimpleGraph W)
namespace FFactor
theorem _root_.solution (U : Set W) (x : W) : Function.Injective (delIncl Γ U x) := by
  intro a b h
  have h' := congrArg Subtype.val h
  exact Subtype.ext h'
end FFactor
