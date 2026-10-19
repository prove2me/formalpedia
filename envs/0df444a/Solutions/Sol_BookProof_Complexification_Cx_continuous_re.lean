-- Prove2me | solution 1 for BookProof.Complexification.Cx.continuous_re
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:23:16.48511+00:00
-- url     : https://prove2.me/submissions/6923fc4f-8bb4-423b-90cd-115511537935

-- Generated from ChapterA1b.lean — solution of BookProof.Complexification.Cx.continuous_re
import Mathlib
import Definitions.Def_ChapterA1b
import Theorems.Thm_BookProof_Complexification_Cx_lipschitz_re
import Definitions.Def_ChapterA
import Definitions.Def_Complexification
open BookProof.Complexification
open BookProof.Complexification.Cx



open scoped RealInnerProductSpace
open BookProof.ChapterA


variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

set_option maxHeartbeats 1000000 in
theorem solution : Continuous (Cx.re : Cx W → W) := lipschitz_re.continuous
