-- Prove2me | solution 1 for FFactor.home_inl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:56:08.698808+00:00
-- url     : https://prove2.me/submissions/949030bc-07d0-4ee7-b2da-8d361e6408ff

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
theorem _root_.solution (d : G.Dart) :
    home G f U (.inl d) = if d.fst ∈ Tset G f U then d.snd else d.fst := rfl
end FFactor
