-- Prove2me | solution 1 for FFactor.home_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:55:44.020333+00:00
-- url     : https://prove2.me/submissions/a9d3bb99-9f74-4b58-a6e1-958152c74ff2

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
theorem _root_.solution (p : Σ v : V, Fin (G.degree v - f v)) :
    home G f U (.inr p) = p.1 := rfl
end FFactor
