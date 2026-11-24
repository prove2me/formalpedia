-- Prove2me | solution 1 for FFactor.F4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:01:31.192465+00:00
-- url     : https://prove2.me/submissions/e0948c08-7210-48e4-aa54-e9d34d0527d9

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
public import Definitions.Def_FFactorLib_FFactorGadget
public import Definitions.Def_FFactorLib_FFactorSuff
public import Theorems.Thm_FFactor_mem_Sset

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {f : V → ℕ}
variable {U : Set (GV G f)}
namespace FFactor
theorem _root_.solution {v : V} (hv : v ∈ Sset G f U) {d : G.Dart} (hd : d.fst = v) :
    (.inl d : GV G f) ∈ U :=
  (mem_Sset.mp hv).2 d hd
end FFactor
