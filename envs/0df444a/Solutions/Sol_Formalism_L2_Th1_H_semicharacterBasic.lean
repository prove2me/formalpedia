-- Prove2me | solution 1 for Formalism.L2.Th1.H.semicharacterBasic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:33.040802+00:00
-- url     : https://prove2.me/submissions/467a8f65-b1ec-48e3-b38a-1e2146b2206a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstUnique
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Theorems.Thm_Formalism_L2_Th1_H_altE_swap
import Theorems.Thm_Formalism_L2_Th1_F_OperatorUThetaLemmas_altE_swap


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
theorem _root_.solution : SemiCharBasic := by
  intro V _ _ H hH Λ α hα
  obtain ⟨hpm, hmul⟩ := hα
  have hA0 : ∀ x, altE H x x = 0 := fun x => Complex.conj_eq_iff_im.mp (hH x x).symm
  have h0 : α 0 = 1 := by
    have h := hmul 0 Λ.zero_mem 0 Λ.zero_mem
    rw [add_zero, hA0, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h
    rcases hpm 0 Λ.zero_mem with h' | h'
    · exact h'
    · rw [h'] at h; norm_num at h
  have hneg : ∀ x ∈ Λ, α (-x) = α x := by
    intro x hx
    have h := hmul x hx (-x) (Λ.neg_mem hx)
    have hA : altE H x (-x) = 0 := by
      have h' := hA0 x
      simp only [altE] at h' ⊢
      rw [map_neg, Complex.neg_im, h', neg_zero]
    rw [add_neg_cancel, h0, hA, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h
    rcases hpm x hx with h1 | h1 <;> rcases hpm (-x) (Λ.neg_mem hx) with h2 | h2 <;>
      rw [h1, h2] at h ⊢ <;> try norm_num at h
  have hdual : Λ ≤ dualLat H Λ := by
    intro x hx
    show ∀ y ∈ Λ, ∃ m : ℤ, altE H x y = (m : ℝ)
    intro y hy
    have e1 := hmul x hx y hy
    have e2 := hmul y hy x hx
    rw [add_comm y x, altE_swap H hH] at e2
    have hxne : α x ≠ 0 := by rcases hpm x hx with h | h <;> rw [h] <;> norm_num
    have hyne : α y ≠ 0 := by rcases hpm y hy with h | h <;> rw [h] <;> norm_num
    have he : Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) =
        Complex.exp ((Real.pi : ℂ) * Complex.I * ((-altE H x y : ℝ) : ℂ)) := by
      have h := e1.symm.trans e2
      rw [mul_comm (α y) (α x)] at h
      exact mul_left_cancel₀ (mul_ne_zero hxne hyne) h
    rw [Complex.exp_eq_exp_iff_exists_int] at he
    obtain ⟨n, hn⟩ := he
    refine ⟨n, ?_⟩
    have hpi : (Real.pi : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero
    push_cast at hn
    have h' : ((altE H x y : ℝ) : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ (mul_ne_zero (two_ne_zero' ℂ) hpi)
      linear_combination hn
    exact_mod_cast h'
  exact ⟨h0, hneg, hdual⟩
end Formalism.L2.Th1.H
