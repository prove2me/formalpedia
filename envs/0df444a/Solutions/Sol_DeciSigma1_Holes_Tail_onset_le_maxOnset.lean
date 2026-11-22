-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.onset_le_maxOnset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:51:43.646543+00:00
-- url     : https://prove2.me/submissions/93f9e067-fc37-4fd1-a394-79ee4ecfa631

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

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers
open DeciSigma1.Words (pow)
open DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
open DeciSigma1.Arithmetic DeciSigma1.Words DeciSigma1.Automata
variable {ι : Type}
variable [DecidableEq α] [Fintype S] (M : StructuralReader α S k) [Fintype ι] [DecidableEq ι]
variable {M}
omit [DecidableEq ι]
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (Ω : ι → Ray α) (i : ι) : (Ω i).onset ≤ maxOnset Ω :=
  Finset.le_sup (f := fun i => (Ω i).onset) (Finset.mem_univ i)
end DeciSigma1.Holes.Tail
