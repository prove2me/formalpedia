-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G3.inner_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:05.147127+00:00
-- url     : https://prove2.me/submissions/f712e85d-5706-4d68-9fad-aac37dc939f3

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Theorems.Thm_Formalism_FourierDecayAlt_P_G3_phase1

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
theorem _root_.solution (β ξ : ℂ) (f : ℂ → ℂ) :
    ∫ x : ℂ, f x * psi β (ξ * x) = 𝓕 f (al β * (starRingEnd ℂ) ξ) := by
  rw [Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [phase1, psi, smul_eq_mul]
  rw [mul_comm (f x), mul_comm Complex.I]
end Formalism.FourierDecayAlt.P.G3
