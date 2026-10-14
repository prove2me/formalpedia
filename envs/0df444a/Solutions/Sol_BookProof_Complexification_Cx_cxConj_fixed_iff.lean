-- Prove2me | solution 1 for BookProof.Complexification.Cx.cxConj_fixed_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T12:18:06.762621+00:00
-- url     : https://prove2.me/submissions/a6ad7202-299a-468e-ad2b-82ce40cff5cf

-- Generated from Complexification.lean — solution of BookProof.Complexification.Cx.cxConj_fixed_iff
import Mathlib
import Definitions.Def_Complexification
import Definitions.Def_ChapterQgOuterFockCoreFL
open BookProof.Complexification
open BookProof.Complexification.Cx



open scoped RealInnerProductSpace
open RCLike


set_option linter.unusedSectionVars false

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

set_option maxHeartbeats 1000000 in
theorem solution (x : Cx W) : cxConj x = x ↔ x.im = 0 := by

  constructor
  · intro h
    have hh : -x.im = x.im := congrArg Cx.im h
    have h0 : x.im + x.im = 0 := neg_eq_iff_add_eq_zero.mp hh
    have h2 : (2 : ℝ) • x.im = 0 := by rw [two_smul]; exact h0
    rcases smul_eq_zero.mp h2 with hc | hc
    · norm_num at hc
    · exact hc
  · intro h; ext <;> simp [h]
