-- Prove2me | solution 1 for FFactor.mem_compl_union_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:53:40.166679+00:00
-- url     : https://prove2.me/submissions/5e371589-8b46-4f9b-81f4-018cd5ec3ccd

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorDefs
public import Definitions.Def_FFactorLib_FFactorNec

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open FFactor
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]
namespace FFactor
theorem _root_.solution {S T : Finset V} {u : V} :
    u ∈ ((S ∪ T : Finset V) : Set V)ᶜ ↔ u ∉ S ∧ u ∉ T := by
  simp
end FFactor
