-- Prove2me | solution 1 for DeciSigma1.Words.Ray.onset_le_of_periodicFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:13:09.829491+00:00
-- url     : https://prove2.me/submissions/e8c41fe3-25f8-401b-91fc-e22777284aeb

module
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Theorems.Thm_DeciSigma1_Words_Ray_stream_add_stem
public import Theorems.Thm_DeciSigma1_Words_Ray_onset_le_stem
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans


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
theorem _root_.solution {A p : ℕ} (hp : 0 < p) (h : PeriodicFrom Ω.stream A p) :
    Ω.onset ≤ A := by
  by_cases hA : Ω.stem.length ≤ A
  · exact onset_le_stem.trans hA
  · apply Nat.find_min' Ω.exists_onsetAt
    rw [onsetAt_iff]
    apply period_of_suffix (k := Ω.stem.length - A) hp h
    intro i
    simp only
    rw [show A + (Ω.stem.length - A + (i + Ω.loop.length)) = Ω.stem.length + (i + Ω.loop.length) by
        omega, show A + (Ω.stem.length - A + i) = Ω.stem.length + i by omega,
      stream_add_stem, stream_add_stem, periodicTail_period_length]
end DeciSigma1.Words.Ray
