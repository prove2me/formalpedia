-- Prove2me | solution 1 for BookProof.MassGap.shiftedSpectrum_vacuum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T15:54:15.914168+00:00
-- url     : https://prove2.me/submissions/e5278037-f11b-475c-9999-99b88b3507c4

-- Generated from ChapterMassGap.lean — solution of BookProof.MassGap.shiftedSpectrum_vacuum
import Mathlib
import Definitions.Def_ChapterMassGap
open BookProof.MassGap


















open scoped BigOperators


variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]




variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (E : Fin (n + 2) → ℝ) (lam : ℝ) :
    shiftedSpectrum E lam 0 = E 0 := by

  unfold shiftedSpectrum numberOp; norm_num;
