-- Prove2me | solution 1 for BookProof.ChapterSirkGramCutoff.gramEigen_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T07:44:03.580142+00:00
-- url     : https://prove2.me/submissions/abe81e96-1ddf-4983-b67d-42d58289def2

-- Generated from ChapterSirkGramCutoff.lean — solution of BookProof.ChapterSirkGramCutoff.gramEigen_nonneg
import Mathlib
import Definitions.Def_ChapterSirkGramCutoff
import Theorems.Thm_BookProof_ChapterSirkGramCutoff_norm_sq_synthesis_gramEigen
open BookProof.ChapterSirkGramCutoff










noncomputable section


open scoped InnerProductSpace
open BookProof.ChapterSirkGramWhitening
open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]






variable {m : ℕ} {w : Fin m → E}
variable {u : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))} {lam : Fin m → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (heig : IsGramEigen w u lam) (k : Fin m) : 0 ≤ lam k := by

  rw [← norm_sq_synthesis_gramEigen heig k]; positivity
