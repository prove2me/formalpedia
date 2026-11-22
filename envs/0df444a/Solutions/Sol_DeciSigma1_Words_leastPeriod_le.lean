-- Prove2me | solution 1 for DeciSigma1.Words.leastPeriod_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:41:13.788654+00:00
-- url     : https://prove2.me/submissions/1a6044fe-c9d6-4213-8678-4b7776730074

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
theorem _root_.solution (hp : 0 < p) (h : w.HasPeriod p) : leastPeriod w ≤ p :=
  Nat.find_min' (exists_pos_period w) ⟨hp, h⟩
end DeciSigma1.Words
