-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.sc_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:09:55.21214+00:00
-- url     : https://prove2.me/submissions/4c9066d9-f735-4fd3-996e-875d6125a7a5

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
theorem _root_.solution {ε x : ℝ} (hε : 0 < ε) (hx : x ≤ ε / 4) : sc ε x = 0 := by
  unfold sc
  exact Real.smoothTransition.zero_of_nonpos (div_nonpos_iff.2 (Or.inr ⟨by linarith, by linarith⟩))
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
