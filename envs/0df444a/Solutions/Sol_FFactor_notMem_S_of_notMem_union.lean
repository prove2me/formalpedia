-- Prove2me | solution 1 for FFactor.notMem_S_of_notMem_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:57:17.317018+00:00
-- url     : https://prove2.me/submissions/0c43084d-895e-407b-9c26-077a16901a91

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
public import Definitions.Def_FFactorLib_FFactorGadget
public import Definitions.Def_FFactorLib_FFactorSuff

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {f : V → ℕ}
variable [DecidableEq V] {U : Set (GV G f)}
namespace FFactor
theorem _root_.solution {r : V} (hr : r ∉ Sset G f U ∪ Tset G f U) :
    r ∉ Sset G f U := fun h => hr (mem_union_left _ h)
end FFactor
