-- Prove2me | solution 1 for FFactor.F2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:03:59.294683+00:00
-- url     : https://prove2.me/submissions/e66546c8-bbd5-46ac-a8d2-18c010d0abd1

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
public import Definitions.Def_FFactorLib_FFactorGadget
public import Definitions.Def_FFactorLib_FFactorSuff
public import Theorems.Thm_FFactor_outer_notMem_of_inner_all

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {f : V → ℕ}
variable {U : Set (GV G f)}
namespace FFactor
theorem _root_.solution (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x) {v : V} (hv : v ∈ Tset G f U)
    {d : G.Dart} (hd : d.fst = v) : (.inl d : GV G f) ∉ U :=
  outer_notMem_of_inner_all hmin (mem_Tset.mp hv) hd
end FFactor
