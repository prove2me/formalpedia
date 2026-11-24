-- Prove2me | solution 1 for Formalism.L2.Th1.H.SemicharacterExponentialLemmas.semi_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:26:13.925564+00:00
-- url     : https://prove2.me/submissions/5de3aa42-6f9f-45cb-8b18-0246d7e1d1d8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_GaussDegenerate
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaussSumEighthPower
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GapStatement
import Theorems.Thm_Formalism_L2_Th1_H_SemicharacterExponentialLemmas_altE_self
import Theorems.Thm_Formalism_L2_Th1_H_SemicharacterExponentialLemmas_altE_nsmul_left
import Theorems.Thm_Formalism_L2_Th1_H_SemicharacterExponentialLemmas_semi_sq

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
open Formalism.L2.Th1.H.SemicharacterExponentialLemmas
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.L2.Th1.H.SemicharacterExponentialLemmas
theorem _root_.solution {H : Sesq V} (hH : IsHerm H) {Λ : AddSubgroup V} {α : V → ℂ}
    (hα : IsSemiChar H Λ α) {x : V} (hx : x ∈ Λ) (k : ℕ) : α (k • x) = α x ^ (k ^ 2) := by
  have hs : α x ^ 2 = 1 := by rw [sq]; exact semi_sq hα hx
  induction k with
  | zero =>
    have h1 := hα.2 0 Λ.zero_mem 0 Λ.zero_mem
    have h2 := semi_sq hα Λ.zero_mem
    simp only [add_zero, altE, map_zero, LinearMap.zero_apply, Complex.zero_im, Complex.ofReal_zero,
      mul_zero, Complex.exp_zero, mul_one] at h1
    rw [zero_nsmul]
    calc α 0 = α 0 * α 0 := h1
      _ = 1 := h2
      _ = α x ^ (0 ^ 2) := by simp
  | succ k ih =>
    have hk : k • x ∈ Λ := Λ.nsmul_mem hx k
    have e := hα.2 (k • x) hk x hx
    have hz : altE H (k • x) x = 0 := by rw [altE_nsmul_left, altE_self H hH, mul_zero]
    rw [succ_nsmul, e, hz, ih]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
    have hk2 : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
    rw [hk2, pow_add, pow_add, pow_mul, hs, one_pow, mul_one, pow_one]
end Formalism.L2.Th1.H.SemicharacterExponentialLemmas
