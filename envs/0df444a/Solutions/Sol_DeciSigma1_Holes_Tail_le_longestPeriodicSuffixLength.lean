-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.le_longestPeriodicSuffixLength
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:56:24.716628+00:00
-- url     : https://prove2.me/submissions/8a59a9ea-3ae9-4bf6-b645-e2ce3f5aab49

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
public import Theorems.Thm_DeciSigma1_Holes_Tail_periodicOn_full_iff

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution [DecidableEq α] {w : List α} {E p s : ℕ} (hp : 0 < p)
    (hpE : p ≤ E)
    (hs : s ≤ w.length) (h : PeriodicOn w p s w.length) : w.length - s ≤
        longestPeriodicSuffixLength E w := by
  unfold longestPeriodicSuffixLength
  apply Finset.le_sup (f := fun s => w.length - s)
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, p, Finset.mem_Icc.mpr ⟨hp, hpE⟩, (periodicOn_full_iff hs).mp h⟩
end DeciSigma1.Holes.Tail
