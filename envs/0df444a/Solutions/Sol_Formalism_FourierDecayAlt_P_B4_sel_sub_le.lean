-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.sel_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:37:20.190364+00:00
-- url     : https://prove2.me/submissions/4ca82163-69f9-42de-9c3d-2b6f8ad13f47

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
theorem _root_.solution (t : ℝ × ℝ) (b : Bool) : |sel t b - 1| ≤ |t.1 - 1| + |t.2 - 1| := by
  cases b <;> simp only [sel] <;> linarith [abs_nonneg (t.1 - 1), abs_nonneg (t.2 - 1)]
end Formalism.FourierDecayAlt.P.B4
