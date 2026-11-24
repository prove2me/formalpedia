-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.sc_cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:13:01.525531+00:00
-- url     : https://prove2.me/submissions/a5df4d03-05a1-4dc4-aab8-f6f86f7f1bf7

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
theorem _root_.solution (ε : ℝ) : ContDiff ℝ ∞ (sc ε) := by
  show ContDiff ℝ ∞ (fun x => Real.smoothTransition ((x - ε / 4) / (ε / 4)))
  exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
