-- Prove2me | solution 1 for BookProof.Complexification.Cx.lipschitz_im
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:50:43.901717+00:00
-- url     : https://prove2.me/submissions/5990b848-9a1b-4868-9b8c-da97471b27b0

import Definitions.Def_ChapterA
import Mathlib
import Definitions.Def_ChapterA1b
import Definitions.Def_Complexification
-- Generated from ChapterA1b.lean — theorem BookProof.Complexification.Cx.lipschitz_im
open BookProof.Complexification
open BookProof.Complexification


open scoped RealInnerProductSpace
open BookProof.ChapterA


variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]


theorem solution : LipschitzWith 1 (Cx.im : Cx W → W) := by
  exact LipschitzWith.of_dist_le_mul (fun x y => by simpa [dist_eq_norm] using Cx.norm_im_le (x - y))

