-- Prove2me | solution 1 for DeciSigma1.Words.Ray.onset_eq_of_stream_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:14:24.102894+00:00
-- url     : https://prove2.me/submissions/fa91208d-ee5f-4af5-99f3-9cda32f1d5c8

module
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Theorems.Thm_DeciSigma1_Words_Ray_onset_le_iff

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
theorem _root_.solution {Ω Ω' : Ray α} (h : ∀ t, Ω.stream t = Ω'.stream t) :
    Ω.onset = Ω'.onset := by
  have hf : Ω.stream = Ω'.stream := funext h
  have key : ∀ A, Ω.onset ≤ A ↔ Ω'.onset ≤ A := by
    intro A; rw [onset_le_iff, onset_le_iff, hf]
  exact le_antisymm ((key _).mpr le_rfl) ((key _).mp le_rfl)
end DeciSigma1.Words.Ray
