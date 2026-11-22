-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.pumpFactor_period_of_snoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:00:08.644577+00:00
-- url     : https://prove2.me/submissions/a7954bb2-915e-43c2-8228-5550d03a2f19

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Theorems.Thm_DeciSigma1_Holes_Tail_length_pumpFactor
public import Theorems.Thm_P2M_DeciSigma1_Holes_Tail_getElem__stay_period_5ce295f93630
public import Theorems.Thm_DeciSigma1_Holes_Tail_pumpFactor_take
public import Theorems.Thm_DeciSigma1_Holes_Tail_take_succ_eq_append
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers
open DeciSigma1.Words (pow)
open DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
variable {T : Table α S k} {q0 : S} {x : List α} {B c c' L : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution {β : Type*} (F : List α → β) (G : β → α → β)
    (hF : ∀ w a, F (w ++ [a]) = G (F w) a) (hcc : c < c') (hc' : c' ≤ x.length)
    (hFc : F (x.take c) = F (x.take c')) (hL : c' - c ≤ L) {p : ℕ} (hp : c ≤ p)
    (hpL : p + (c' - c) ≤ c + L) :
    F ((pumpFactor x c c' L).take (p + (c' - c))) = F ((pumpFactor x c c' L).take p) := by
  have hlen := length_pumpFactor (L := L) hcc hc'
  induction p, hp using Nat.le_induction with
  | base =>
    rw [show c + (c' - c) = c' by omega, pumpFactor_take hcc hc' hL le_rfl,
      pumpFactor_take hcc hc' hL hcc.le]
    exact hFc.symm
  | succ p hp ih =>
    have hlet := getElem?_stay_period hcc hc' hp (by omega : p + (c' - c) < c + L)
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
      Option.some_inj] at hlet
    rw [show p + 1 + (c' - c) = p + (c' - c) + 1 by omega, take_succ_eq_append (by omega),
      take_succ_eq_append (by omega), hF, hF, ih (by omega), hlet]
end DeciSigma1.Holes.Tail
