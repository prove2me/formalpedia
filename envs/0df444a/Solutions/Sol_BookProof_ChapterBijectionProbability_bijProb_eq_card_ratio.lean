-- Prove2me | solution 1 for BookProof.ChapterBijectionProbability.bijProb_eq_card_ratio
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:28:19.118737+00:00
-- url     : https://prove2.me/submissions/7e723876-c14e-4bdb-9f0d-f70c79ee5de7

-- Generated from ChapterBijectionProbability.lean — solution of BookProof.ChapterBijectionProbability.bijProb_eq_card_ratio
import Mathlib
import Definitions.Def_ChapterBijectionProbability
import Theorems.Thm_BookProof_ChapterBijectionProbability_card_fun_fin
import Theorems.Thm_BookProof_ChapterBijectionProbability_card_bijective_fin
open BookProof.ChapterBijectionProbability



open scoped Nat
open Filter Asymptotics

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) :
    bijProb n =
      (Fintype.card {f : Fin n → Fin n // Function.Bijective f} : ℝ)
        / (Fintype.card (Fin n → Fin n) : ℝ) := by

  rw [card_bijective_fin, card_fun_fin, bijProb]
  push_cast
  ring
