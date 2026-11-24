-- Prove2me | solution 1 for FFactor.fst_notMem_S_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:03:15.106096+00:00
-- url     : https://prove2.me/submissions/4c87d55b-99cf-4763-9dbe-3ce0ed4991be

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
public import Definitions.Def_FFactorLib_FFactorGadget
public import Definitions.Def_FFactorLib_FFactorSuff
public import Theorems.Thm_FFactor_F4

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {f : V → ℕ}
variable [DecidableEq V] {U : Set (GV G f)}
omit [DecidableEq V]
namespace FFactor
theorem _root_.solution {d : G.Dart} (hd : (.inl d : GV G f) ∉ U) :
    d.fst ∉ Sset G f U := fun h => hd (F4 h rfl)
end FFactor
