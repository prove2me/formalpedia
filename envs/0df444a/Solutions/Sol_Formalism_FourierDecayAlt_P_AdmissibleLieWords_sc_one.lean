-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.sc_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:15:42.592349+00:00
-- url     : https://prove2.me/submissions/89ed22aa-f8c1-44a3-bd31-218c707eb79a

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
theorem _root_.solution {ε x : ℝ} (hε : 0 < ε) (hx : ε / 2 ≤ x) : sc ε x = 1 := by
  unfold sc
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by linarith)]
  linarith
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
