-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.op_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:37:26.06603+00:00
-- url     : https://prove2.me/submissions/bf66cd61-862b-46d1-a66d-bf7976e3d688

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure

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
theorem _root_.solution (b : Bool) (X : Mat k r) (a : ℂ) (f : Mat k r → E) : op b X (a • f) = a • op b X f := by
  funext g
  simp only [op, Pi.smul_apply]
  first
    | exact deriv_const_smul' (f := fun t : ℝ => f (cv b X t g)) (x := 0) a
    | exact deriv_const_smul_field (f := fun t : ℝ => f (cv b X t g)) (x := 0) a
end Formalism.FourierDecayAlt.P.B4
