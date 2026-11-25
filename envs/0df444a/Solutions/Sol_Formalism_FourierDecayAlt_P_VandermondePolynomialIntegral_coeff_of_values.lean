-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral.coeff_of_values
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:14:54.182713+00:00
-- url     : https://prove2.me/submissions/7fdbca39-e8e7-4150-81a6-609d3e88cec2

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoeffOfValues
import Theorems.Thm_Formalism_FourierDecayAlt_P_VandermondePolynomialIntegral_vN_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
variable {E : Type*} [AddCommGroup E] [Module ℂ E]
namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
theorem _root_.solution (d : ℕ) (c : Fin (d + 1) → E) (n : Fin (d + 1)) :
    ∑ m, (vN d)⁻¹ n m • ∑ n' : Fin (d + 1), ((((m : ℕ) : ℝ) : ℂ) ^ (n' : ℕ)) • c n' = c n := by
  have hinv : (vN d)⁻¹ * vN d = 1 := Matrix.nonsing_inv_mul _ (vN_det d)
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have e : ∀ n' : Fin (d + 1), ∑ m, ((vN d)⁻¹ n m * (((m : ℕ) : ℝ) : ℂ) ^ (n' : ℕ)) • c n' =
      ((vN d)⁻¹ * vN d) n n' • c n' := by
    intro n'
    rw [← Finset.sum_smul, Matrix.mul_apply]
    congr 1
  simp_rw [e, hinv, Matrix.one_apply, ite_smul, one_smul, zero_smul]
  simp
end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
