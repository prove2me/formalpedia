-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G3.double_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:51.442626+00:00
-- url     : https://prove2.me/submissions/09ab4df4-e303-40cf-beae-9825bcfed9b9

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Theorems.Thm_Formalism_FourierDecayAlt_P_G3_double_vol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory
open scoped FourierTransform RealInnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G3
namespace Formalism.FourierDecayAlt.P.G3
theorem _root_.solution (β : ℂ) (hβ : β ≠ 0) (κ : NNReal) (f : SchwartzMap ℂ ℂ) (w : ℂ) :
    ∫ ξ : ℂ, (∫ x : ℂ, f x * psi β (ξ * x) ∂(κ • (volume : Measure ℂ))) * psi β (w * ξ)
        ∂(κ • (volume : Measure ℂ)) =
      (((κ : ℝ) ^ 2 * ((‖β‖ / (2 * Real.pi)) ^ 2)⁻¹ : ℝ) : ℂ) * f (-w) := by
  simp only [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul, mul_assoc]
  rw [integral_const_mul, double_vol β hβ]
  simp only [Complex.real_smul]
  push_cast
  ring
end Formalism.FourierDecayAlt.P.G3
