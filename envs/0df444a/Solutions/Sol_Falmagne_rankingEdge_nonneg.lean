-- Prove2me | solution 1 for Falmagne.rankingEdge_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:13:59.669314+00:00
-- url     : https://prove2.me/submissions/03e0f09b-5748-486b-bca8-e711c10f080f

module
public import Definitions.Def_EconomicsNextProof_Basic
public import Definitions.Def_EconomicsNextProof_Representation

set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {l : List X} {A : Finset X} {x : X}
namespace Falmagne
theorem _root_.solution (l : List X) (x : X) (A : Finset X) :
    0 ≤ rankingEdge l x A := by
  unfold rankingEdge
  split <;> norm_num
end Falmagne
