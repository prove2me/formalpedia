-- Prove2me | solution 1 for FFactor.gadget_adj_inr_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:52:07.226781+00:00
-- url     : https://prove2.me/submissions/73cc4484-ae49-4293-a176-368277b28079

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
theorem _root_.solution {p q : Σ v : V, Fin (G.degree v - f v)} :
    ¬ (gadget G f).Adj (.inr p) (.inr q) := id
end FFactor
