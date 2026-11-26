-- Prove2me | solution 1 for Falmagne.lawFlow_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:14:34.322813+00:00
-- url     : https://prove2.me/submissions/d835b968-8bd2-4019-88e9-6f2aa7ef6ad9

module
public import Definitions.Def_EconomicsNextProof_Basic
public import Definitions.Def_EconomicsNextProof_Representation
public import Theorems.Thm_Falmagne_rankingEdge_nonneg

set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {l : List X} {A : Finset X} {x : X}
namespace Falmagne
theorem _root_.solution {w : RankingLaw X} (hw : ∀ l, 0 ≤ w l) (x : X) (A : Finset X) :
    0 ≤ lawFlow w x A := by
  unfold lawFlow Finsupp.sum
  exact Finset.sum_nonneg fun l _ => mul_nonneg (hw l) (rankingEdge_nonneg l x A)
end Falmagne
