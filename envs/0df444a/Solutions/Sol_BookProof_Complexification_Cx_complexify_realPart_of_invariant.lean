-- Prove2me | solution 1 for BookProof.Complexification.Cx.complexify_realPart_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:23:22.163244+00:00
-- url     : https://prove2.me/submissions/6a477458-695e-47d8-9373-e44440c1f8af

-- Generated from ChapterA1b.lean — solution of BookProof.Complexification.Cx.complexify_realPart_of_invariant
import Mathlib
import Definitions.Def_ChapterA1b
import Theorems.Thm_BookProof_Complexification_Cx_eq_ofReal_add_smul
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
theorem solution {X : Submodule ℂ (Cx W)}
    (hX : ∀ x ∈ X, cxConj x ∈ X) : complexify (realPart X) = X := by

  refine le_antisymm ?_ ?_
  · -- `complexify (realPart X) ⊆ X`
    rw [SetLike.le_def]
    rintro x ⟨hxre, hxim⟩
    rw [eq_ofReal_add_smul x]
    exact X.add_mem hxre (X.smul_mem _ hxim)
  · -- `X ⊆ complexify (realPart X)`
    rw [SetLike.le_def]
    intro x hx
    refine ⟨?_, ?_⟩
    · -- `ofReal x.re = ½ (x + cxConj x) ∈ X`
      change ofReal x.re ∈ X
      have h : ofReal x.re = (2⁻¹ : ℂ) • (x + cxConj x) := by
        ext
        · simp [cxConj_apply, csmul_re]; module
        · simp [cxConj_apply, csmul_im]
      rw [h]; exact X.smul_mem _ (X.add_mem hx (hX x hx))
    · -- `ofReal x.im = (-½ i) (x - cxConj x) ∈ X`
      change ofReal x.im ∈ X
      have h : ofReal x.im = (-(2⁻¹ : ℂ) * Complex.I) • (x - cxConj x) := by
        ext
        · simp [cxConj_apply, csmul_re, Complex.mul_re, Complex.mul_im]; module
        · simp [cxConj_apply, csmul_im, Complex.mul_re, Complex.mul_im]
      rw [h]; exact X.smul_mem _ (X.sub_mem hx (hX x hx))
