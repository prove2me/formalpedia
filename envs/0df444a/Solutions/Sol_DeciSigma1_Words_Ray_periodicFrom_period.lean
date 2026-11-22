-- Prove2me | solution 1 for DeciSigma1.Words.Ray.periodicFrom_period
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:58:49.893533+00:00
-- url     : https://prove2.me/submissions/094cf248-b417-4331-8a1f-920fd2e1af46

module
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Words (pow)
variable {α : Type}
open DeciSigma1.Words.Ray
variable (Ω : Ray α)
variable {Ω}
variable [DecidableEq α]
namespace DeciSigma1.Words.Ray
theorem _root_.solution (Ω : Ray α) : PeriodicFrom Ω.stream Ω.onset Ω.period :=
  (leastStreamPeriod_shift (Ω := Ω) le_rfl).2.1
end DeciSigma1.Words.Ray
