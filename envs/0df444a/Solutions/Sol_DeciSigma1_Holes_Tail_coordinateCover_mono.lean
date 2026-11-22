-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.coordinateCover_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:55:42.290541+00:00
-- url     : https://prove2.me/submissions/2ca4c881-a31c-4540-bd71-8dc548680d15

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Theorems.Thm_DeciSigma1_Holes_Tail_PeriodicCover_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_NoSuffixOccurrenceEndsBetween_mono
public import Theorems.Thm_DeciSigma1_Words_ChainBoundFrom_mono
public import Theorems.Thm_DeciSigma1_Words_ChainBound_mono
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_mono


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
variable {σ N : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (C : LevelBounds σ k N) {l l' : ℕ} (hl : l ≤ l')
    {M : StructuralReader α S k}
    {W : Fin k → List α} {i : Fin k} (h : CoordinateCover C l M W i) : CoordinateCover C l' M W i :=
  PeriodicCover.mono h le_rfl (C.periodBound_mono hl) (C.uncoveredBound_mono hl)
end DeciSigma1.Holes.Tail
