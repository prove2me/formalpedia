-- Prove2me | solution 1 for FFactor.gadget_adj_inl_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:51:54.550338+00:00
-- url     : https://prove2.me/submissions/460509a3-28f5-4a46-8152-a442e57292e3

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
    (gadget G f).Adj (.inl d) (.inr p) ↔ d.fst = p.1 := Iff.rfl
end FFactor
