-- Prove2me | solution 1 for BookProof.Complexification.Cx.continuous_im
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:23:17.865759+00:00
-- url     : https://prove2.me/submissions/79d18f81-4002-420d-9e8e-cc8dea21cf5f

-- Generated from ChapterA1b.lean — solution of BookProof.Complexification.Cx.continuous_im
import Mathlib
import Definitions.Def_ChapterA1b
import Theorems.Thm_BookProof_Complexification_Cx_lipschitz_im
import Definitions.Def_ChapterA
import Definitions.Def_Complexification
open BookProof.Complexification
open BookProof.Complexification.Cx



open scoped RealInnerProductSpace
open BookProof.ChapterA


variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

set_option maxHeartbeats 1000000 in
theorem solution : Continuous (Cx.im : Cx W → W) := lipschitz_im.continuous
