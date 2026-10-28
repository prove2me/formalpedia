-- Prove2me | solution 1 for BookProof.QgOuterFockOneParticle.oneParticleOp_herm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T06:10:49.138306+00:00
-- url     : https://prove2.me/submissions/44752f39-28b8-4ca0-ba9a-4d724c73f400

-- Generated from ChapterQgOuterFockOneParticle.lean — theorem BookProof.QgOuterFockOneParticle.oneParticleOp_herm
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Mathlib
import Definitions.Def_ChapterQgOuterFockOneParticle
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterQgOuterFockFlow
open BookProof.ScalaronEsa



open MeasureTheory
open BookProof.FarisLavine BookProof.ScalaronEsa
open BookProof.DirectSumEsa BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL

noncomputable section

variable {ι : Type*} [DecidableEq ι] (W : WallPot) (Q : QgModeData ι)
open BookProof.QgOuterFockOneParticle in
theorem solution (a b : ι) (v u : ccDomain ℝ) :
    (inner ℂ (oneParticleOp W Q b a v) ((u : L2R)) : ℂ)
      = inner ℂ (v : L2R) (oneParticleOp W Q a b u) := by
  rw [oneParticleOp_apply, oneParticleOp_apply, Q.A_herm a b, Q.B_herm a b]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_conj,
    xCc_symmetricOn v u]
  by_cases h : a = b
  · subst h; simp only [if_true]; rw [W.ham_symmetricOn]
  · simp [h, Ne.symm h]
