-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.pumpFactor_letter_period
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:00:03.154575+00:00
-- url     : https://prove2.me/submissions/de7aeb8f-2799-42c1-80ba-150d6425fb1e

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
public import Theorems.Thm_P2M_DeciSigma1_Holes_Tail_getElem__pumpFactor_of_lt_90a7620e9ffe
public import Theorems.Thm_P2M_DeciSigma1_Holes_Tail_getElem__stay_period_5ce295f93630
public import Theorems.Thm_DeciSigma1_Holes_Tail_ClosedAt_window
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
theorem _root_.solution (hcl : ClosedAt T q0 x B c c') (hL : c' - c ≤ L) {p : ℕ}
    (hp : c - B ≤ p) (hpL : p + (c' - c) < c + L) :
    (pumpFactor x c c' L)[p]? = (pumpFactor x c c' L)[p + (c' - c)]? := by
  have ⟨hB, hcc, hc', _⟩ := hcl
  by_cases hpc : p < c
  · rw [getElem?_pumpFactor_of_lt hcc hc' hL (by omega),
      getElem?_pumpFactor_of_lt hcc hc' hL (by omega)]
    have := hcl.window (j := p - (c - B)) (by omega)
    rwa [show c - B + (p - (c - B)) = p by omega,
      show c' - B + (p - (c - B)) = p + (c' - c) by omega] at this
  · exact (getElem?_stay_period hcc hc' (by omega) hpL).symm
end DeciSigma1.Holes.Tail
