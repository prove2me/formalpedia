-- Prove2me | solution 1 for BookProof.Complexification.Cx.lipschitz_re
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:50:28.739869+00:00
-- url     : https://prove2.me/submissions/b86d52fd-4a22-4a27-a0b9-1834f152cbff

import Definitions.Def_ChapterA
import Mathlib
import Definitions.Def_ChapterA1b
import Definitions.Def_Complexification
-- Generated from ChapterA1b.lean — theorem BookProof.Complexification.Cx.lipschitz_re
open BookProof.Complexification
open BookProof.Complexification


open scoped RealInnerProductSpace
open BookProof.ChapterA


variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]


theorem solution : LipschitzWith 1 (Cx.re : Cx W → W) := by
  exact LipschitzWith.of_dist_le_mul (fun x y => by simpa [dist_eq_norm] using Cx.norm_re_le (x - y))

