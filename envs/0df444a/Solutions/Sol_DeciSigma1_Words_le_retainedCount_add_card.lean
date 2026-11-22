-- Prove2me | solution 1 for DeciSigma1.Words.le_retainedCount_add_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:44:54.332138+00:00
-- url     : https://prove2.me/submissions/6409573a-3255-4d9d-bb60-79137313d343

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
theorem _root_.solution (a : ℕ) : a ≤ retainedCount D a + D.card := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.range a) (· ∈ D)
  have hD : ((Finset.range a).filter (· ∈ D)).card ≤ D.card :=
    Finset.card_le_card fun p hp => (Finset.mem_filter.mp hp).2
  rw [Finset.card_range] at h
  unfold retainedCount
  omega
end DeciSigma1.Words
