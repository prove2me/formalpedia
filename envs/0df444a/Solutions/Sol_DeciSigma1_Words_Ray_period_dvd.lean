-- Prove2me | solution 1 for DeciSigma1.Words.Ray.period_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:13:46.0795+00:00
-- url     : https://prove2.me/submissions/52a4d0e8-d4cb-480a-a9aa-16faec0402a6

module
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Theorems.Thm_DeciSigma1_Words_leastPeriod_dvd_iff

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
theorem _root_.solution : Ω.period ∣ Ω.loop.length :=
  (leastPeriod_dvd_iff leastStreamPeriod_periodicTail).mp periodicTail_period_length
end DeciSigma1.Words.Ray
