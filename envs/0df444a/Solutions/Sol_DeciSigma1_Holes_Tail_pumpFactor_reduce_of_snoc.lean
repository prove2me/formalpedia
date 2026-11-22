-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.pumpFactor_reduce_of_snoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:00:55.968469+00:00
-- url     : https://prove2.me/submissions/dd09b134-5ccb-430c-97eb-8e3f8bb5756c

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
public import Theorems.Thm_DeciSigma1_Holes_Tail_pumpFactor_take
public import Theorems.Thm_DeciSigma1_Holes_Tail_pumpFactor_period_of_snoc
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans


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
    (hFc : F (x.take c) = F (x.take c')) (hL : c' - c ≤ L) :
    ∀ p ≤ c + L, ∃ p' ≤ c', (c < p → c < p') ∧
      F ((pumpFactor x c c' L).take p) = F (x.take p') := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp
    by_cases h1 : p ≤ c'
    · exact ⟨p, h1, id, by rw [pumpFactor_take hcc hc' hL h1]⟩
    · have hst := pumpFactor_period_of_snoc F G hF hcc hc' hFc hL (p := p - (c' - c)) (by omega)
        (by omega)
      rw [show p - (c' - c) + (c' - c) = p by omega] at hst
      obtain ⟨p', hp', hc, he⟩ := ih (p - (c' - c)) (by omega) (by omega)
      exact ⟨p', hp', fun _ => hc (by omega), hst.trans he⟩
end DeciSigma1.Holes.Tail
