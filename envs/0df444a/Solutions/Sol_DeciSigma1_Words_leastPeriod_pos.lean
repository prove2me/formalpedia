-- Prove2me | solution 1 for DeciSigma1.Words.leastPeriod_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:41:12.02547+00:00
-- url     : https://prove2.me/submissions/2ce42bcf-c580-4bf3-8189-a6f7dd8182ff

module
public import Mathlib.Data.List.PeriodicityLemma
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
variable {α : Type*}
variable [DecidableEq α] {w : List α} {p g : ℕ}
namespace DeciSigma1.Words
theorem _root_.solution (w : List α) : 0 < leastPeriod w :=
  (Nat.find_spec (exists_pos_period w)).1
end DeciSigma1.Words
