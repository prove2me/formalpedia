-- Prove2me | solution 2 for BookProof.Complexification.Cx.continuous_re
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:50:53.894291+00:00
-- url     : https://prove2.me/submissions/9ede07fa-883c-4e7c-81fa-fcf49af6fd77

import Definitions.Def_ChapterA
import Mathlib
import Definitions.Def_ChapterA1b
import Definitions.Def_Complexification
-- Generated from ChapterA1b.lean — theorem BookProof.Complexification.Cx.continuous_re
open BookProof.Complexification
open BookProof.Complexification


open scoped RealInnerProductSpace
open BookProof.ChapterA


variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]


theorem solution : Continuous (Cx.re : Cx W → W) := by
  exact (LipschitzWith.of_dist_le_mul (K := 1) (fun x y => by simpa [dist_eq_norm] using Cx.norm_re_le (x - y))).continuous

