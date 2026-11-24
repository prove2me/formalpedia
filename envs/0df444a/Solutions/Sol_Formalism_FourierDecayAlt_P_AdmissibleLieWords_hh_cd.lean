-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.hh_cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:40:51.215483+00:00
-- url     : https://prove2.me/submissions/32f165f7-d230-403c-8285-ae3d225a4278

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplLen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_PolynomialBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfUnitWords
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_sc_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_sc_cd

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
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (hh ε) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : ε / 8 < x
  · have hx0 : 0 < x := by linarith
    show ContDiffAt ℝ ∞ (fun y => sc ε y * y ^ (-(1 / 2 : ℝ))) x
    exact ((sc_cd ε).contDiffAt).mul (Real.contDiffAt_rpow_const_of_ne hx0.ne')
  · have h0 : hh ε =ᶠ[nhds x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show x < ε / 4 by linarith)] with y hy
      simp [hh, sc_zero hε (le_of_lt hy)]
    exact contDiffAt_const.congr_of_eventuallyEq h0
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
