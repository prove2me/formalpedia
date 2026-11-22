-- Prove2me | solution 1 for DeciSigma1.Words.Ray.length_suffixBeforeOnset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:39:41.580048+00:00
-- url     : https://prove2.me/submissions/e0aebed6-f989-4d1e-b108-89856005c2d8

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
theorem _root_.solution (Ω : Ray α) (J : ℕ) :
    (Ω.suffixBeforeOnset J).length = Ω.onset - J := by simp [suffixBeforeOnset]
end DeciSigma1.Words.Ray
