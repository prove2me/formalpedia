-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.periodicOn_take
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:03:06.192604+00:00
-- url     : https://prove2.me/submissions/92dfd111-56f2-49af-adfd-f6914af91fe8

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_TerminalRays
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayCompatibility

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Arithmetic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution {w : List α} {p s e n : ℕ} (h : PeriodicOn w p s e) (hen : e ≤ n) :
    PeriodicOn (w.take n) p s e := by
  intro x hx hxe
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_take_of_lt (by omega)]
  exact h x hx hxe
end DeciSigma1.Holes.Tail
