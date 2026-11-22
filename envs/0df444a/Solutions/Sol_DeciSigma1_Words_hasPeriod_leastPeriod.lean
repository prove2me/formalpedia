-- Prove2me | solution 1 for DeciSigma1.Words.hasPeriod_leastPeriod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:38:50.556549+00:00
-- url     : https://prove2.me/submissions/a63dd6f4-4d06-493c-a3b4-72c79d42295d

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
theorem _root_.solution (w : List α) : w.HasPeriod (leastPeriod w) :=
  (Nat.find_spec (exists_pos_period w)).2
end DeciSigma1.Words
