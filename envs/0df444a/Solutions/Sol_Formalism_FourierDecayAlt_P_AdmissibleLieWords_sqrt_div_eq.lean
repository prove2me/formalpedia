-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.sqrt_div_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:09:55.941618+00:00
-- url     : https://prove2.me/submissions/fb23fbd6-16bf-4662-8408-2c6b4ecdcdff

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplLen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolynomialBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfUnitWords

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
theorem _root_.solution {T x : ℝ} (hT : 0 < T) (hx : 0 < x) : Real.sqrt (T / x) = Real.sqrt T * x ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_div hT.le x, Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
