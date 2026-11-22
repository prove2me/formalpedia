-- Prove2me | solution 1 for DeciSigma1.Words.retainedCount_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:44:35.56558+00:00
-- url     : https://prove2.me/submissions/f26cf464-f263-45af-8c33-a8030910d9db

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}
namespace DeciSigma1.Words
theorem _root_.solution {D' : Finset ℕ} {a : ℕ} (h : ∀ p < a, p ∈ D ↔ p ∈ D') :
    retainedCount D a = retainedCount D' a := by
  unfold retainedCount
  congr 1
  exact Finset.filter_congr fun p hp => not_congr (h p (Finset.mem_range.mp hp))
end DeciSigma1.Words
