-- Prove2me | solution 1 for Falmagne.mobius_eq_lawFlow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:15:57.58349+00:00
-- url     : https://prove2.me/submissions/17dd7b00-2fb0-4c52-8f7f-e30e1900f7ca

module
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_Mobius
public import Definitions.Def_EconomicsNextProof_ChoiceMobius
public import Theorems.Thm_Falmagne_upperSum_lawFlow
public import Theorems.Thm_EconomicsNextProof_upperMobius_upperSum


set_option autoImplicit true
@[expose] public section
public section
open Falmagne
open EconomicsNextProof
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {l : List X} {A : Finset X} {x : X}
namespace Falmagne
theorem _root_.solution {w : RankingLaw X} {p : Finset X → X → ℝ}
    (hw : ∀ l ∈ w.support, IsRanking l) (hp : Represents w p) (x : X) (A : Finset X)
    (hx : x ∈ A) :
    upperMobius (fun B => p B x) A = lawFlow w x A := by
  calc
    _ = upperMobius (upperSum (lawFlow w x)) A := by
      unfold upperMobius
      apply Finset.sum_congr rfl
      intro B hB
      have hAB : A ⊆ B := (Finset.mem_filter.mp hB).2
      rw [upperSum_lawFlow w hw x B (hAB hx)]
      change _ * p B x = _
      rw [hp B x]
    _ = lawFlow w x A := congrFun (upperMobius_upperSum (lawFlow w x)) A
end Falmagne
