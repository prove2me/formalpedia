-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.pat_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:09:16.988789+00:00
-- url     : https://prove2.me/submissions/69754e2c-e374-420b-a616-422b6cc078ee

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Filter Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.QRR
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.QRR
theorem _root_.solution {l : Fin r} {A : Mx k r} (hA : Pat k r l A) : Pat k r l (-A) := by
  intro i j h
  apply hA
  intro h0
  apply h
  rw [Matrix.neg_apply, h0, neg_zero]
end Formalism.FourierDecayAlt.Q.QRR
