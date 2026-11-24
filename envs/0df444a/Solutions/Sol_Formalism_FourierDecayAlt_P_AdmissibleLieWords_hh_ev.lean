-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.hh_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:34:50.766596+00:00
-- url     : https://prove2.me/submissions/e7742cf4-7a8a-4e8e-85d2-b1f0eea05c69

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplLen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolynomialBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfUnitWords
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_sc_one

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
theorem _root_.solution {ε x : ℝ} (hε : 0 < ε) (hx : ε / 2 < x) :
    hh ε =ᶠ[nhds x] fun y => y ^ (-(1 / 2 : ℝ)) := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  simp only [hh, sc_one hε (le_of_lt hy), one_mul]
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
