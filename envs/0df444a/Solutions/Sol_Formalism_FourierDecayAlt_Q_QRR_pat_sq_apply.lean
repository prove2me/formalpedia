-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.pat_sq_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:38:06.896264+00:00
-- url     : https://prove2.me/submissions/66fa80e1-b0d2-4273-ba12-2eaa84c477b5

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
theorem _root_.solution {l : Fin r} {Y : Mx k r} (hY : Pat k r l Y) (i j : Fin (2 * r + k + 1))
    (h : ¬ (i.val = l.val ∧ j.val = 2 * r + k - l.val)) : (Y * Y) i j = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro m _
  by_cases h1 : Y i m = 0
  · rw [h1, zero_mul]
  · by_cases h2 : Y m j = 0
    · rw [h2, mul_zero]
    · exfalso
      have e1 := hY i m h1
      have e2 := hY m j h2
      have := l.isLt
      omega
end Formalism.FourierDecayAlt.Q.QRR
