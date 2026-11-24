-- Prove2me | solution 1 for FFactor.gadget_adj_inl_inl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:51:56.226807+00:00
-- url     : https://prove2.me/submissions/2785c6b0-9e2e-474b-a614-517f25518865

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorGadget

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] (G : SimpleGraph V) (f : V → ℕ)
namespace FFactor
theorem _root_.solution {d d' : G.Dart} :
    (gadget G f).Adj (.inl d) (.inl d') ↔ d' = d.symm := Iff.rfl
end FFactor
