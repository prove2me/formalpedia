-- Prove2me | solution 1 for DeciSigma1.Words.PeriodicOn.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:34:27.392158+00:00
-- url     : https://prove2.me/submissions/6f8b6fa9-7976-44ec-8594-00967445ed59

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
open DeciSigma1.Words.PeriodicOn
variable {w : List α} {d s e : ℕ}
namespace DeciSigma1.Words.PeriodicOn
theorem _root_.solution {s' e' : ℕ} (h : PeriodicOn w d s e) (hs : s ≤ s') (he : e' ≤ e) :
    PeriodicOn w d s' e' :=
  fun p hp hpe => h p (hs.trans hp) (by omega)
end DeciSigma1.Words.PeriodicOn
