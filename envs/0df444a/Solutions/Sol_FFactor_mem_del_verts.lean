-- Prove2me | solution 1 for FFactor.mem_del_verts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:51:33.2868+00:00
-- url     : https://prove2.me/submissions/f6ee0d9f-8053-448c-a8dc-057fcecdd0f9

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open FFactor
variable {W : Type*} (Γ : SimpleGraph W)
namespace FFactor
theorem _root_.solution {U : Set W} {a : W} :
    a ∈ ((⊤ : Γ.Subgraph).deleteVerts U).verts ↔ a ∉ U := by simp
end FFactor
