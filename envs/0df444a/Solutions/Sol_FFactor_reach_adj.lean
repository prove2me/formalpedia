-- Prove2me | solution 1 for FFactor.reach_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:57:16.803823+00:00
-- url     : https://prove2.me/submissions/789ff1ca-1578-4f53-92fe-6d6337892364

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
public import Definitions.Def_FFactorLib_FFactorGadget
public import Definitions.Def_FFactorLib_FFactorSuff
public import Theorems.Thm_FFactor_mem_del_verts
attribute [local simp] FFactor.mem_del_verts



set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {f : V → ℕ}
variable [DecidableEq V] {U : Set (GV G f)}
omit [DecidableEq V]
namespace FFactor
theorem _root_.solution {a b : GV G f} (ha : a ∉ U) (hb : b ∉ U) (h : (gadget G f).Adj a b) :
    (del (gadget G f) U).Reachable ⟨a, (mem_del_verts _).mpr ha⟩
      ⟨b, (mem_del_verts _).mpr hb⟩ :=
  Adj.reachable ((del_adj _).mpr h)
end FFactor
