-- Prove2me | solution 1 for BookProof.Complexification.Cx.eq_ofReal_add_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:23:20.621526+00:00
-- url     : https://prove2.me/submissions/db574b24-51b4-4e86-b0cf-b83043e66d17

-- Generated from ChapterA1b.lean — solution of BookProof.Complexification.Cx.eq_ofReal_add_smul
import Mathlib
import Definitions.Def_ChapterA1b
import Theorems.Thm_BookProof_Complexification_Cx_smul_I
import Definitions.Def_ChapterA
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_Complexification
open BookProof.Complexification
open BookProof.Complexification.Cx



open scoped RealInnerProductSpace
open BookProof.ChapterA
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData


variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

set_option maxHeartbeats 1000000 in
theorem solution (x : Cx W) : x = ofReal x.re + (Complex.I : ℂ) • ofReal x.im := by

  rw [smul_I]; ext <;> simp
