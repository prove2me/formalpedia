-- Prove2me | solution 1 for BrooksTheorem.Aux.mem_of_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:37:35.434197+00:00
-- url     : https://prove2.me/submissions/fde751b0-afa8-4cf6-a73d-6b6989090064

module
public import Definitions.Def_BrooksLib_BrooksCore
public import Definitions.Def_BrooksLib_Cycle
public import Definitions.Def_BrooksLib_BrooksLow

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*} [Fintype V]
omit [Fintype V]
namespace BrooksTheorem.Aux
theorem _root_.solution (G : SimpleGraph V) (hconn : G.Connected) (C : Set V) {v0 : V}
    (hv0 : v0 ∈ C) (hC : ∀ u ∈ C, ∀ w, G.Adj u w → w ∈ C) (w : V) : w ∈ C := by
  have key : ∀ {a b : V} (p : G.Walk a b), a ∈ C → b ∈ C := by
    intro a b p
    induction p with
    | nil => exact id
    | cons h _ ihp => exact fun ha => ihp (hC _ ha _ h)
  exact key (hconn.preconnected v0 w).some hv0
end BrooksTheorem.Aux
