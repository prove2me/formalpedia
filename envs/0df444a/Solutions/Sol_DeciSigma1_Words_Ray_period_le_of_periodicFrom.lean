-- Prove2me | solution 1 for DeciSigma1.Words.Ray.period_le_of_periodicFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:52.133736+00:00
-- url     : https://prove2.me/submissions/3ea5914c-e3f8-4cac-9375-706235ef2af7

module
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_mono


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
theorem _root_.solution {Ω : Ray α} {A p : ℕ} (hp : 0 < p)
    (h : PeriodicFrom Ω.stream A p) :
    Ω.period ≤ p := by
  have h1 := leastStreamPeriod_shift (Ω := Ω) (A := max A Ω.onset) (le_max_right _ _)
  exact h1.2.2 p hp (h.mono (le_max_left _ _))
end DeciSigma1.Words.Ray
