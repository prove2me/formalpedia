-- Prove2me | solution 1 for Formalism.L2.Th1.H.gauss_plane
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:26:17.355119+00:00
-- url     : https://prove2.me/submissions/9bddfe80-f4f4-4894-a246-481c8265ab3f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyIdentity
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyGaussianIntegral

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
open MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution (l : ℂ) (hl : 0 < l.re) :
    Integrable (fun z : ℂ => Complex.exp (-((Real.pi : ℂ) * l) * ((‖z‖ : ℝ) : ℂ) ^ 2)) ∧
      ∫ z : ℂ, Complex.exp (-((Real.pi : ℂ) * l) * ((‖z‖ : ℝ) : ℂ) ^ 2) = l⁻¹ := by
  have hl0 : l ≠ 0 := fun h => by simp [h] at hl
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hb : 0 < ((Real.pi : ℂ) * l).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos Real.pi_pos hl
  refine ⟨?_, ?_⟩
  · have := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) hb 0 (0 : ℂ)
    simpa using this
  · rw [GaussianFourier.integral_cexp_neg_mul_sq_norm (V := ℂ) hb, Complex.finrank_real_complex]
    rw [show ((2 : ℕ) : ℂ) / 2 = 1 by norm_num, Complex.cpow_one]
    field_simp
end Formalism.L2.Th1.H
