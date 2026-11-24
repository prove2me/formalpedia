-- Prove2me | solution 1 for FFactor.not_isTutteViolator_iff_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:04:31.05941+00:00
-- url     : https://prove2.me/submissions/b8e3e861-b8f4-4ab9-8340-e3a6a235b85b

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorDefs
public import Definitions.Def_FFactorLib_FFactorSuff
public import Definitions.Def_FFactorLib_FFactorCount

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {f : V → ℕ}
  {U : Set (GV G f)}
omit [DecidableEq V]
namespace FFactor
theorem _root_.solution {U' : Set (GV G f)} :
    (gadget G f).IsTutteViolator U' ↔ U'.ncard < (del (gadget G f) U').oddComponents.ncard :=
  Iff.rfl
end FFactor
