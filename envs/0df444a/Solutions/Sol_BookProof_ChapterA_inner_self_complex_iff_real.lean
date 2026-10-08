-- Prove2me | solution 1 for BookProof.ChapterA.inner_self_complex_iff_real
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:03:12.43567+00:00
-- url     : https://prove2.me/submissions/cb18b6d8-9603-43df-b5a0-8aaddf33e44d

-- Generated from ChapterA1Prop5.lean — theorem BookProof.ChapterA.inner_self_complex_iff_real
import Mathlib
import Definitions.Def_ChapterA1Prop5
import Definitions.Def_ChapterA
open BookProof.ChapterA

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace





attribute [local instance] InnerProductSpace.rclikeToReal

theorem solution (T : H₁ → H₂) :
    (∀ x, (inner ℂ (T x) (T x) : ℂ) = (inner ℂ x x : ℂ)) ↔
    (∀ x, (inner ℝ (T x) (T x) : ℝ) = (inner ℝ x x : ℝ)) := by
  simp only [real_inner_eq_re_inner ℂ]
  constructor
  · intro h x
    exact congrArg Complex.re (h x)
  · intro h x
    apply Complex.ext
    · exact h x
    · change RCLike.im (inner ℂ (T x) (T x)) = RCLike.im (inner ℂ x x)
      rw [inner_self_im, inner_self_im]


#print axioms solution
