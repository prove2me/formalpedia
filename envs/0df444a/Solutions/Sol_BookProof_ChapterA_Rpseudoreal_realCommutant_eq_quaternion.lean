-- Prove2me | solution 1 for BookProof.ChapterA.Rpseudoreal_realCommutant_eq_quaternion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T08:01:12.714988+00:00
-- url     : https://prove2.me/submissions/2b941a15-0ee2-42bc-9b33-8fbcf8e81535

import Mathlib
import Definitions.Def_ChapterA2c
import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
import Theorems.Thm_BookProof_ChapterA_Plin_add_Qanti
import Theorems.Thm_BookProof_ChapterA_Plin_commutes_mulI
import Theorems.Thm_BookProof_ChapterA_Plin_realCommutes
import Theorems.Thm_BookProof_ChapterA_Qanti_anticommutes_mulI
import Theorems.Thm_BookProof_ChapterA_Qanti_realCommutes
import Theorems.Thm_BookProof_ChapterA_qembed_apply
import Theorems.Thm_BookProof_ChapterA_qembed_realCommutes
import Theorems.Thm_BookProof_ChapterA_cplxify_commutes
import Theorems.Thm_BookProof_ChapterA_realCommutes_mul
import Theorems.Thm_BookProof_ChapterA_realCommutes_thetaR
-- Generated from ChapterA2c.lean — theorem BookProof.ChapterA.Rpseudoreal_realCommutant_eq_quaternion
open BookProof.ChapterA
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]


theorem solution (M : System ℂ V) (hSchur : IsSchurFull M)
    {θ : AntiUnitary V} (hθ : ∀ x, θ (θ x) = -x) (hθc : CommutesAntiUnitary M θ)
    (S : V →L[ℝ] V) :
    RealCommutes M S ↔ ∃ q : Quaternion ℝ, S = qembed θ hθ q := by
  constructor
  · intro hS
    obtain ⟨c, hc⟩ := hSchur _ (BookProof.ChapterA.cplxify_commutes (BookProof.ChapterA.Plin_commutes_mulI S)
      (BookProof.ChapterA.Plin_realCommutes hS))
    have hPx : ∀ x, Plin S x = c • x := by
      intro x
      have := congrArg (fun F : V →L[ℂ] V => F x) hc
      simpa using this
    have hθI : ∀ x, θ (Complex.I • x) = -(Complex.I • θ x) := by
      intro x
      rw [θ.map_smulₛₗ]; simp
    have hT : ∀ x, (Qanti S * thetaR θ) (Complex.I • x) = Complex.I • (Qanti S * thetaR θ) x := by
      intro x
      simp only [ContinuousLinearMap.mul_apply, thetaR_apply]
      rw [hθI, map_neg, BookProof.ChapterA.Qanti_anticommutes_mulI, neg_neg]
    obtain ⟨d, hd⟩ := hSchur _ (BookProof.ChapterA.cplxify_commutes hT
      (BookProof.ChapterA.realCommutes_mul (BookProof.ChapterA.Qanti_realCommutes hS)
        (BookProof.ChapterA.realCommutes_thetaR hθc)))
    have hTx : ∀ x, Qanti S (θ x) = d • x := by
      intro x
      have := congrArg (fun F : V →L[ℂ] V => F x) hd
      simpa using this
    have hQx : ∀ x, Qanti S x = -(d • θ x) := by
      intro x
      have h1 := hTx (θ x)
      rw [hθ, map_neg] at h1
      rw [← h1, neg_neg]
    refine ⟨(⟨c.re, c.im, -d.re, -d.im⟩ : Quaternion ℝ), ?_⟩
    ext x
    erw [BookProof.ChapterA.qembed_apply]
    have hSx : S x = Plin S x + Qanti S x := by
      rw [← ContinuousLinearMap.add_apply, BookProof.ChapterA.Plin_add_Qanti]
    rw [hSx, hPx, hQx]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply,
      mulI_apply, thetaR_apply, Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.one_apply]
    conv_lhs => rw [← Complex.re_add_im c, ← Complex.re_add_im d]
    simp only [add_smul, mul_smul, ← Complex.coe_smul, neg_add, neg_smul, smul_neg]
    abel
  · rintro ⟨q, rfl⟩
    exact BookProof.ChapterA.qembed_realCommutes hθ hθc q

