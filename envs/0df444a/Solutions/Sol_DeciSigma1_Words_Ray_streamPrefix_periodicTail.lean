-- Prove2me | solution 1 for DeciSigma1.Words.Ray.streamPrefix_periodicTail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:13:04.651542+00:00
-- url     : https://prove2.me/submissions/6195c6ab-a6e2-4e6c-9ff2-dca4de4af1df

module
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset

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
omit [DecidableEq α]
namespace DeciSigma1.Words.Ray
theorem _root_.solution (L : ℕ) :
    streamPrefix Ω.periodicTail L = (pow Ω.loop (L + 1)).take L := by
  have hn := Ω.loop_length_pos
  apply List.ext_getElem?
  intro i
  by_cases hi : i < L
  · rw [List.getElem?_take_of_lt hi, getElem?_pow Ω.loop_ne_nil
      (by rw [length_pow]; nlinarith),
      List.getElem?_eq_getElem (by simpa using hi), List.getElem?_eq_getElem (Nat.mod_lt _ hn)]
    simp [hi, periodicTail]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
end DeciSigma1.Words.Ray
