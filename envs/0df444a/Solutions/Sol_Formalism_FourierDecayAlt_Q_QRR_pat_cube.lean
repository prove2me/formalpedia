-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.pat_cube
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:55:12.68479+00:00
-- url     : https://prove2.me/submissions/168556dc-f261-4764-8b08-1bd0edce1d53

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_pat_sq_apply

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
theorem _root_.solution {l : Fin r} {Y : Mx k r} (hY : Pat k r l Y) : Y ^ 3 = 0 := by
  ext i j
  rw [pow_three', Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro m _
  by_cases h1 : i.val = l.val ∧ m.val = 2 * r + k - l.val
  · have h2 : Y m j = 0 := by
      by_contra h0
      have e := hY m j h0
      have := l.isLt
      omega
    rw [h2, mul_zero]
  · rw [pat_sq_apply hY i m h1, zero_mul]
end Formalism.FourierDecayAlt.Q.QRR
