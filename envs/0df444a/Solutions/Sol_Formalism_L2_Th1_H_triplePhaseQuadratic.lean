-- Prove2me | solution 1 for Formalism.L2.Th1.H.triplePhaseQuadratic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:44:08.676877+00:00
-- url     : https://prove2.me/submissions/ff67b5de-db75-4620-9362-961827e6c10d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_GaussDegenerate
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaussSumEighthPower
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GapStatement
import Theorems.Thm_Formalism_L2_Th1_H_SemicharacterExponentialLemmas_altE_add_left
import Theorems.Thm_Formalism_L2_Th1_H_SemicharacterExponentialLemmas_altE_add_right
import Theorems.Thm_Formalism_L2_Th1_H_SemicharacterExponentialLemmas_altE_neg_right
import Theorems.Thm_Formalism_L2_Th1_H_SemicharacterExponentialLemmas_altE_self
import Theorems.Thm_Formalism_L2_Th1_H_SemicharacterExponentialLemmas_altE_nsmul_left
import Theorems.Thm_Formalism_L2_Th1_H_SemicharacterExponentialLemmas_altE_nsmul_right
import Theorems.Thm_Formalism_L2_Th1_H_SemicharacterExponentialLemmas_exp_eq_of_int
import Theorems.Thm_Formalism_L2_Th1_H_SemicharacterExponentialLemmas_semi_sq
import Theorems.Thm_Formalism_L2_Th1_H_SemicharacterExponentialLemmas_semi_norm
import Theorems.Thm_Formalism_L2_Th1_H_SemicharacterExponentialLemmas_semi_nsmul
import Theorems.Thm_Formalism_L2_Th1_F_LegendreModelEllipticTorsion_key
import Theorems.Thm_Formalism_L2_Th1_F_OperatorUThetaLemmas_altE_swap
import Theorems.Thm_Formalism_L2_Th1_H_altE_swap
import Theorems.Thm_Formalism_L2_Th1_H_semicharacterBasic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
open SemicharacterExponentialLemmas
namespace Formalism.L2.Th1.H
theorem _root_.solution : PsiQuadratic := by
  intro V _ _ H α Λ₁ Λ₂ Λ₃ hT
  have hH := hT.herm
  have int₁ := (semicharacterBasic V H hH Λ₁ α hT.sc₁).2.2
  have int₂ := (semicharacterBasic V H hH Λ₂ α hT.sc₂).2.2
  have int₃ := (semicharacterBasic V H hH Λ₃ α hT.sc₃).2.2
  have hadd : ∀ z ∈ Λ₃, ∀ y ∈ Λ₂, z + y ∈ Λ₁ → ∀ z' ∈ Λ₃, ∀ y' ∈ Λ₂, z' + y' ∈ Λ₁ →
      psiT H α (z + z') (y + y') = psiT H α z y * psiT H α z' y'
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H y z' : ℂ)) := by
    intro z hz y hy hzy z' hz' y' hy' hzy'
    obtain ⟨m, hm⟩ := int₃ hz z' hz'
    obtain ⟨k, hk⟩ := int₂ hy y' hy'
    have hsw := altE_swap H hH y z'
    simp only [psiT]
    rw [show z + z' + (y + y') = (z + y) + (z' + y') by abel, hT.sc₃.2 z hz z' hz',
      hT.sc₂.2 y hy y' hy', hT.sc₁.2 _ hzy _ hzy']
    have key : Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H z z' : ℂ))
        * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H y y' : ℂ))
        * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H (z + y) (z' + y') : ℂ))
        * Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H (z + z') (y + y') : ℂ))
        = Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H z y : ℂ))
        * Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H z' y' : ℂ))
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H y z' : ℂ)) := by
      simp only [← Complex.exp_add]
      apply exp_eq_of_int (m + k)
      simp only [altE_add_left, altE_add_right, hsw, hm, hk]
      push_cast
      ring
    linear_combination (α z * α z' * α y * α y' * α (z + y) * α (z' + y')) * key
  refine ⟨hadd, ?_, ?_, ?_⟩
  · intro z hz y hy hzy k
    simp only [psiT]
    rw [← smul_add, semi_nsmul hH hT.sc₃ hz, semi_nsmul hH hT.sc₂ hy, semi_nsmul hH hT.sc₁ hzy,
      altE_nsmul_left, altE_nsmul_right, mul_pow, mul_pow, mul_pow, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring
  · intro z hz y hy hzy
    simp only [psiT]
    rw [norm_mul, norm_mul, norm_mul, semi_norm hT.sc₃ hz, semi_norm hT.sc₂ hy,
      semi_norm hT.sc₁ hzy,
      show -(Real.pi : ℂ) * Complex.I * (altE H z y : ℂ)
        = ((-Real.pi * altE H z y : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
    norm_num
  · intro z hz y hy hzy u' hu' u hu t ht
    have hz' : u' + t ∈ Λ₃ := Λ₃.add_mem hu'.2 ht.2
    have hy' : u - t ∈ Λ₂ := Λ₂.sub_mem hu.2 ht.1
    have hzy' : u' + t + (u - t) ∈ Λ₁ := by
      rw [show u' + t + (u - t) = u' + u by abel]
      exact Λ₁.add_mem hu'.1 hu.1
    rw [show z + u' + t = z + (u' + t) by abel, show y + u - t = y + (u - t) by abel,
      hadd z hz y hy hzy _ hz' _ hy' hzy']
    have h1 : psiT H α (u' + t) (u - t) = 1 := by
      obtain ⟨m, hm⟩ := int₃ hu'.2 t ht.2
      have hsw := altE_swap H hH u t
      have hneg := (semicharacterBasic V H hH Λ₂ α hT.sc₂).2.1 t ht.1
      simp only [psiT]
      rw [show u' + t + (u - t) = u' + u by abel, sub_eq_add_neg, hT.sc₃.2 u' hu'.2 t ht.2,
        hT.sc₂.2 u hu.2 (-t) (Λ₂.neg_mem ht.1), hT.sc₁.2 u' hu'.1 u hu.1, hneg]
      have key : Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H u' t : ℂ))
          * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H u (-t) : ℂ))
          * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H u' u : ℂ))
          * Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H (u' + t) (u + -t) : ℂ)) = 1 := by
        simp only [← Complex.exp_add]
        rw [← Complex.exp_zero]
        apply exp_eq_of_int m
        simp only [altE_add_left, altE_add_right, altE_neg_right, hsw, hm, altE_self H hH t]
        push_cast
        ring
      have a1 := semi_sq hT.sc₁ hu'.1
      have a2 := semi_sq hT.sc₂ hu.2
      have a3 := semi_sq hT.sc₂ ht.1
      calc _ = (α u' * α u') * (α u * α u) * (α t * α t)
            * (Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H u' t : ℂ))
          * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H u (-t) : ℂ))
          * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H u' u : ℂ))
          * Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H (u' + t) (u + -t) : ℂ))) := by ring
        _ = 1 := by rw [key, a1, a2, a3]; norm_num
    have h2 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H y (u' + t) : ℂ)) = 1 := by
      obtain ⟨m, hm⟩ := int₂ hy t ht.1
      obtain ⟨k, hk⟩ := int₁ hzy u' hu'.1
      obtain ⟨l, hl⟩ := int₃ hz u' hu'.2
      rw [altE_add_left] at hk
      have hyu : altE H y u' = (k : ℝ) - (l : ℝ) := by linarith
      rw [← Complex.exp_zero]
      apply exp_eq_of_int (k - l + m)
      rw [altE_add_right, hyu, hm]
      push_cast
      ring
    rw [h1, h2, mul_one, mul_one]
end Formalism.L2.Th1.H
