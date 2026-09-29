-- Prove2me | solution 1 for BookProof.ChapterSirkGramWhitening.synthesis_injective_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T06:43:29.587327+00:00
-- url     : https://prove2.me/submissions/030059eb-59e1-4aa0-8697-294cef302e23

-- Generated from ChapterSirkGramWhitening.lean — solution of BookProof.ChapterSirkGramWhitening.synthesis_injective_of_linearIndependent
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening









noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {m : ℕ} {w : Fin m → E}
    (hw : LinearIndependent ℂ w) : Function.Injective (synthesis w) := by

  rw [injective_iff_map_eq_zero]
  intro c hc
  have hc' : ∑ i, (c i) • w i = 0 := hc
  have hzero := (Fintype.linearIndependent_iff.mp hw) (fun i => c i) hc'
  ext i
  simpa using hzero i
