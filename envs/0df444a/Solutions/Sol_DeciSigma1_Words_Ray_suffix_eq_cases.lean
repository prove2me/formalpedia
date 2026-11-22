-- Prove2me | solution 1 for DeciSigma1.Words.Ray.suffix_eq_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:14:23.619891+00:00
-- url     : https://prove2.me/submissions/b6d83dfa-ae98-49a8-acc2-40e949c43c71

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
theorem _root_.solution {Ω' : Ray α} {a b : ℕ} (h : ∀ t, Ω.stream (a + t) = Ω'.stream (b + t)) :
    (Ω.onset ≤ a ∧ Ω'.onset ≤ b) ∨ (a < Ω.onset ∧ Ω.onset - a = Ω'.onset - b) := by
  have hper : ∀ m p, PeriodicFrom Ω.stream (a + m) p ↔ PeriodicFrom Ω'.stream (b + m) p := by
    intro m p
    unfold PeriodicFrom StreamPeriod
    simp only
    constructor
    · intro hp i
      rw [show b + m + (i + p) = b + (m + i + p) by ring, show b + m + i = b + (m + i) by ring,
        ← h, ← h]
      have := hp i
      rwa [show a + m + (i + p) = a + (m + i + p) by ring,
        show a + m + i = a + (m + i) by ring] at this
    · intro hp i
      rw [show a + m + (i + p) = a + (m + i + p) by ring, show a + m + i = a + (m + i) by ring,
        h, h]
      have := hp i
      rwa [show b + m + (i + p) = b + (m + i + p) by ring,
        show b + m + i = b + (m + i) by ring] at this
  have key : ∀ m, Ω.onset ≤ a + m ↔ Ω'.onset ≤ b + m := by
    intro m
    rw [onset_le_iff, onset_le_iff]
    exact exists_congr fun p => and_congr_right fun _ => hper m p
  have e1 := (key (Ω.onset - a)).mp (by omega)
  have e2 := (key (Ω'.onset - b)).mpr (by omega)
  by_cases ha : Ω.onset ≤ a
  · left; exact ⟨ha, by omega⟩
  · right; exact ⟨by omega, by omega⟩
end DeciSigma1.Words.Ray
