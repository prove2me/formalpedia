-- Prove2me | solution 1 for BookProof.ChapterA.prop5_linear
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:26:00.031966+00:00
-- url     : https://prove2.me/submissions/21292d55-5293-4481-b82a-273d30145f71

-- Generated from ChapterA1Prop5.lean — theorem BookProof.ChapterA.prop5_linear
import Mathlib
import Definitions.Def_ChapterA1Prop5
import Definitions.Def_ChapterA
open BookProof.ChapterA

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace





attribute [local instance] InnerProductSpace.rclikeToReal

theorem solution (U : H₁ →ₗ[ℂ] H₂) :
    (Function.Surjective U ∧ ∀ x, (inner ℂ (U x) (U x) : ℂ) = (inner ℂ x x : ℂ)) ↔
    (Function.Surjective U ∧ ∀ x, (inner ℝ (U x) (U x) : ℝ) = (inner ℝ x x : ℝ)) := by
  simp only [real_inner_eq_re_inner ℂ]
  constructor
  · rintro ⟨hs, h⟩
    exact ⟨hs, fun x => congrArg Complex.re (h x)⟩
  · rintro ⟨hs, h⟩
    refine ⟨hs, fun x => ?_⟩
    apply Complex.ext
    · exact h x
    · change RCLike.im (inner ℂ (U x) (U x)) = RCLike.im (inner ℂ x x)
      rw [inner_self_im, inner_self_im]

#print axioms solution

