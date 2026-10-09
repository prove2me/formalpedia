-- Prove2me | solution 1 for BookProof.ChapterBijectionProbability.card_bijective_fin
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:28:06.093441+00:00
-- url     : https://prove2.me/submissions/ce5d3e1c-5a86-4a53-aa9e-8f19cf173e8e

-- Generated from ChapterBijectionProbability.lean — solution of BookProof.ChapterBijectionProbability.card_bijective_fin
import Mathlib
import Definitions.Def_ChapterBijectionProbability
open BookProof.ChapterBijectionProbability



open scoped Nat
open Filter Asymptotics

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) :
    Fintype.card {f : Fin n → Fin n // Function.Bijective f} = n ! := by

  rw [← Fintype.card_congr (permEquivBijective n), Fintype.card_perm, Fintype.card_fin]
