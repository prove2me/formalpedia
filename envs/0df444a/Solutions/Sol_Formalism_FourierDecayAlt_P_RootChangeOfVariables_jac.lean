-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RootChangeOfVariables.jac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:50:47.624732+00:00
-- url     : https://prove2.me/submissions/31e3b8e8-a066-41ec-bdad-3d15396c3371

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LinearChangeOfVariablesBis
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourthWeightDensityOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JacobianAeNonzero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt MeasureTheory
open scoped ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.RootChangeOfVariables
namespace Formalism.FourierDecayAlt.P.RootChangeOfVariables
theorem _root_.solution (c : ℂ) :
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ : ℂ →L[ℝ] ℂ).det = Complex.normSq c := by
  have e : ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ : ℂ →L[ℝ] ℂ).toLinearMap =
      (LinearMap.mulLeft ℂ c).restrictScalars ℝ := by
    ext x; simp [mul_comm]
  rw [ContinuousLinearMap.det, e, LinearMap.det_restrictScalars, LinearMap.det_mulLeft,
    Algebra.norm_complex_apply]
end Formalism.FourierDecayAlt.P.RootChangeOfVariables
