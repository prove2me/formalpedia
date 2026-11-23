-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G9.core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:59.903993+00:00
-- url     : https://prove2.me/submissions/dce2a0e1-ed1f-4b1e-924f-c68c55003b0a

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Theorems.Thm_Formalism_FourierDecayAlt_P_G9_sqrt_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G9
namespace Formalism.FourierDecayAlt.P.G9
theorem _root_.solution (δ r : ℝ) (hδ : 0 < δ) :
    ∫ w : ℂ, ((Real.exp (-δ * ‖w‖ ^ 2) : ℝ) : ℂ) * Complex.exp (Complex.I * ((r * (w ^ 2).re : ℝ) : ℂ)) =
      ((Real.pi / Real.sqrt (δ ^ 2 + r ^ 2) : ℝ) : ℂ) := by
  rw [← Complex.volume_preserving_equiv_real_prod.symm.integral_comp
    Complex.measurableEquivRealProd.symm.measurableEmbedding]
  have h : ∀ p : ℝ × ℝ,
      ((Real.exp (-δ * ‖Complex.measurableEquivRealProd.symm p‖ ^ 2) : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((r * ((Complex.measurableEquivRealProd.symm p) ^ 2).re : ℝ) : ℂ)) =
      Complex.exp (-((δ : ℂ) - r * Complex.I) * (p.1 : ℂ) ^ 2) *
        Complex.exp (-((δ : ℂ) + r * Complex.I) * (p.2 : ℂ) ^ 2) := by
    rintro ⟨x, y⟩
    have e : Complex.measurableEquivRealProd.symm (x, y) = ⟨x, y⟩ := rfl
    rw [e, ← Complex.normSq_eq_norm_sq, Complex.normSq_mk, Complex.ofReal_exp, ← Complex.exp_add,
      ← Complex.exp_add]
    congr 1
    simp only [pow_two, Complex.mul_re]
    push_cast
    ring
  simp_rw [h]
  rw [Measure.volume_eq_prod, integral_prod_mul (fun x : ℝ => Complex.exp (-((δ : ℂ) - r * Complex.I) * (x : ℂ) ^ 2))
    (fun y : ℝ => Complex.exp (-((δ : ℂ) + r * Complex.I) * (y : ℂ) ^ 2)),
    integral_gaussian_complex (by simpa using hδ), integral_gaussian_complex (by simpa using hδ)]
  exact sqrt_prod δ r hδ
end Formalism.FourierDecayAlt.P.G9
