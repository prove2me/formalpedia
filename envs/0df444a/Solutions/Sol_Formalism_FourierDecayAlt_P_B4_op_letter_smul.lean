-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.op_letter_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:59:08.175415+00:00
-- url     : https://prove2.me/submissions/4ad8e545-8405-4d63-af59-2bff8831c0d5

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_rsmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution (b : Bool) (X : Mat k r) (c : ℝ) (f : Mat k r → E) :
    op b ((c : ℂ) • X) f = c • op b X f := by
  funext g
  simp only [op, Pi.smul_apply]
  simp_rw [cv_rsmul]
  have := deriv_comp_mul_left c (fun s => f (cv b X s g)) 0
  simpa [mul_zero] using this
end Formalism.FourierDecayAlt.P.B4
