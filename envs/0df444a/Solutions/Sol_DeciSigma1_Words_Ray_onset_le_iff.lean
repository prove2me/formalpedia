-- Prove2me | solution 1 for DeciSigma1.Words.Ray.onset_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:13:45.470427+00:00
-- url     : https://prove2.me/submissions/536b8ed8-da78-4e60-a068-103730dfaf66

module
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Theorems.Thm_DeciSigma1_Words_Ray_onset_le_of_periodicFrom

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
theorem _root_.solution {A : ℕ} : Ω.onset ≤ A ↔ ∃ p, 0 < p ∧ PeriodicFrom Ω.stream A p :=
  ⟨fun h => ⟨_, Ω.loop_length_pos, periodicFrom_of_onset_le h⟩,
    fun ⟨_, hp, h⟩ => onset_le_of_periodicFrom hp h⟩
end DeciSigma1.Words.Ray
