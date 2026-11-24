-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.Phh_cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:00:35.108208+00:00
-- url     : https://prove2.me/submissions/db0436d2-759b-4011-aad7-c697cd31e6be

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplLen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolynomialBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfUnitWords
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_hh_cd

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
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (Phh ε) := by
  show ContDiff ℝ ∞ (fun z : ℂ => ((hh ε z.re : ℝ) : ℂ))
  exact Complex.ofRealCLM.contDiff.comp ((hh_cd hε).comp Complex.reCLM.contDiff)
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
