-- Prove2me | solution 1 for BookProof.ChapterSirkGramCutoff.synthesis_single
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T10:44:08.137385+00:00
-- url     : https://prove2.me/submissions/fb79f112-db44-47c3-98fd-7879640516da

import Mathlib
import Definitions.Def_ChapterSirkGramCutoff
open BookProof.ChapterSirkGramCutoff
noncomputable section
open scoped InnerProductSpace
open BookProof.ChapterSirkGramWhitening
open ContinuousLinearMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {m : ℕ} {w : Fin m → E}
variable {u : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))} {lam : Fin m → ℝ}

theorem solution (i : Fin m) :
    synthesis w (EuclideanSpace.single i (1 : ℂ)) = w i := by
  simp [synthesis]
