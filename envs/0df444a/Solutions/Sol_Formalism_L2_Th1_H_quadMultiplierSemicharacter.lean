-- Prove2me | solution 1 for Formalism.L2.Th1.H.quadMultiplierSemicharacter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:44:02.206548+00:00
-- url     : https://prove2.me/submissions/ecb8bc9c-233a-4f81-9cd1-f48a9d65cc91

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
import Theorems.Thm_Formalism_L2_Th1_H_exp_pi_I_int
import Theorems.Thm_Formalism_L2_Th1_F_LegendreModelEllipticTorsion_key
import Theorems.Thm_Formalism_L2_Th1_F_OperatorUThetaLemmas_altE_swap
import Theorems.Thm_Formalism_L2_Th1_H_altE_swap
import Theorems.Thm_Formalism_L2_Th1_H_re_swap


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
namespace Formalism.L2.Th1.H
theorem _root_.solution : AlphaQSemi := by
  intro V _ _ H hH b d hb Λ hdual hstab
  have key : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ k e : ℤ, altE H x y = (e : ℝ) ∧
      Real.sqrt d * (H x y).re = 2 * (k : ℝ) - (b : ℝ) * (e : ℝ) := by
    intro x hx y hy
    obtain ⟨e, he⟩ := hdual hx y hy
    obtain ⟨k, hk⟩ := hdual (hstab x hx) y hy
    refine ⟨k, e, he, ?_⟩
    have hθ : Formalism.L2.Th1.F.cmTheta b d = ⟨(b : ℝ) / 2, Real.sqrt d / 2⟩ := by
      apply Complex.ext <;> simp [Formalism.L2.Th1.F.cmTheta]
    simp only [altE, map_smul, LinearMap.smul_apply, smul_eq_mul, hθ, Complex.mul_im] at hk he
    rw [he] at hk
    linarith
  have hq : ∀ x ∈ Λ, ∃ m : ℤ, qOf (Real.sqrt d / 2) H x = (m : ℝ) := by
    intro x hx
    obtain ⟨k, e, he, hk⟩ := key x hx x hx
    have him : altE H x x = 0 := by
      have := altE_swap H hH x x
      linarith
    rw [him] at he
    refine ⟨k, ?_⟩
    rw [← he] at hk
    simp only [qOf]
    linarith
  have hadd : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ m : ℤ, qOf (Real.sqrt d / 2) H (x + y) - qOf (Real.sqrt d / 2) H x
        - qOf (Real.sqrt d / 2) H y - altE H x y = 2 * (m : ℝ) := by
    intro x hx y hy
    obtain ⟨k, e, he, hk⟩ := key x hx y hy
    obtain ⟨t, rfl⟩ := hb
    refine ⟨k - (t + 1) * e, ?_⟩
    have hs := re_swap H hH x y
    simp only [qOf, map_add, LinearMap.add_apply, Complex.add_re]
    rw [hs, he]
    push_cast at hk ⊢
    linarith
  refine ⟨hq, hadd, ?_, ?_⟩
  · intro x hx
    obtain ⟨m, hm⟩ := hq x hx
    simp only [alphaQ, hm]
    exact_mod_cast exp_pi_I_int m
  · intro x hx y hy
    obtain ⟨m, hm⟩ := hadd x hx y hy
    have h1 : qOf (Real.sqrt d / 2) H (x + y)
        = qOf (Real.sqrt d / 2) H x + qOf (Real.sqrt d / 2) H y + altE H x y + 2 * (m : ℝ) := by
      linarith
    simp only [alphaQ]
    rw [h1, ← Complex.exp_add, ← Complex.exp_add]
    have h2 : (Real.pi : ℂ) * Complex.I * ((qOf (Real.sqrt d / 2) H x + qOf (Real.sqrt d / 2) H y
          + altE H x y + 2 * (m : ℝ) : ℝ) : ℂ)
        = ((Real.pi : ℂ) * Complex.I * (qOf (Real.sqrt d / 2) H x : ℂ)
          + (Real.pi : ℂ) * Complex.I * (qOf (Real.sqrt d / 2) H y : ℂ)
          + (Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) + (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [h2, Complex.exp_add _ ((m : ℂ) * _), Complex.exp_int_mul_two_pi_mul_I, mul_one]
end Formalism.L2.Th1.H
