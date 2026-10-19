-- Prove2me | solution 2 for BookProof.Complexification.Cx.continuous_im
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:51:05.701023+00:00
-- url     : https://prove2.me/submissions/1ba46fb3-da3f-46d7-a19a-c217d1908c31

import Definitions.Def_ChapterA
import Mathlib
import Definitions.Def_ChapterA1b
import Definitions.Def_Complexification
-- Generated from ChapterA1b.lean — theorem BookProof.Complexification.Cx.continuous_im
open BookProof.Complexification
open BookProof.Complexification


open scoped RealInnerProductSpace
open BookProof.ChapterA


variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]


theorem solution : Continuous (Cx.im : Cx W → W) := by
  exact (LipschitzWith.of_dist_le_mul (K := 1) (fun x y => by simpa [dist_eq_norm] using Cx.norm_im_le (x - y))).continuous

