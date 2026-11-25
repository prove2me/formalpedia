-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.fourier_transform_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:53:00.151807+00:00
-- url     : https://prove2.me/submissions/6f0b24cc-4aad-4ac4-a73b-4927883aa83c

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonJointFirstReduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open MeasureTheory Formalism.H
open scoped FourierTransform ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.J.TransformAtZero := by
  intro V _ _ _ _ _ φ
  first
    | (simp [Real.fourier_eq]; done)
    | (simp [Real.fourierIntegral_eq']; done)
    | (simp [Real.fourierIntegral_eq]; done)
    | (simp [Real.fourierIntegral, VectorFourier.fourierIntegral]; done)
    | (simp [FourierTransform.fourier, Real.fourierIntegral, VectorFourier.fourierIntegral]; done)
    | (simp [VectorFourier.fourierIntegral]; done)
end Formalism.FourierDecayAlt.P
