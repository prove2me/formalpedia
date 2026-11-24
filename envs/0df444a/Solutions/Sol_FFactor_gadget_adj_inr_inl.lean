-- Prove2me | solution 1 for FFactor.gadget_adj_inr_inl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:51:43.707299+00:00
-- url     : https://prove2.me/submissions/4d2bf44b-a976-4f61-87e5-cdd579d81ede

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
theorem _root_.solution {d : G.Dart} {p : Σ v : V, Fin (G.degree v - f v)} :
    (gadget G f).Adj (.inr p) (.inl d) ↔ d.fst = p.1 := Iff.rfl
end FFactor
