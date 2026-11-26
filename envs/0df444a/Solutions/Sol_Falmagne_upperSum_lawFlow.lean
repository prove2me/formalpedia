-- Prove2me | solution 1 for Falmagne.upperSum_lawFlow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:15:21.801635+00:00
-- url     : https://prove2.me/submissions/f499ab6c-5ea5-4d07-9c65-489213d4139b

module
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_Mobius
public import Definitions.Def_EconomicsNextProof_ChoiceMobius
public import Theorems.Thm_Falmagne_upperSum_rankingEdge

set_option autoImplicit true
@[expose] public section
public section
open Falmagne
open EconomicsNextProof
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {l : List X} {A : Finset X} {x : X}
namespace Falmagne
theorem _root_.solution (w : RankingLaw X) (hw : ∀ l ∈ w.support, IsRanking l)
    (x : X) (A : Finset X) (hx : x ∈ A) :
    upperSum (lawFlow w x) A = w.sum (fun l a => a * rankingChoice l A x) := by
  unfold upperSum lawFlow Finsupp.sum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  rw [← Finset.mul_sum]
  congr 1
  exact upperSum_rankingEdge (hw l hl) x A hx
end Falmagne
