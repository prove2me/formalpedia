-- Prove2me | solution 1 for BookProof.ChapterSirkGramWhitening.inner_gramOp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T06:34:24.284425+00:00
-- url     : https://prove2.me/submissions/188ae9eb-af38-4372-af78-16198329e022

-- Generated from ChapterSirkGramWhitening.lean — solution of BookProof.ChapterSirkGramWhitening.inner_gramOp
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening









noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {m : ℕ} (w : Fin m → E) (c d : EuclideanSpace ℂ (Fin m)) :
    ⟪c, gramOp w d⟫_ℂ = ⟪synthesis w c, synthesis w d⟫_ℂ := by

  exact ContinuousLinearMap.adjoint_inner_right (synthesis w) c (synthesis w d)
