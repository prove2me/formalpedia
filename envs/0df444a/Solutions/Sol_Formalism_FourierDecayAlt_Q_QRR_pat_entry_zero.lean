-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.pat_entry_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:55:14.921256+00:00
-- url     : https://prove2.me/submissions/bee6aca8-2db4-4b89-b70b-0a9406b9abc2

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
    (h : ¬ ((i.val = l.val ∧ l.val < j.val ∧ j.val ≤ 2 * r + k - l.val) ∨
      (j.val = 2 * r + k - l.val ∧ l.val ≤ i.val ∧ i.val < 2 * r + k - l.val))) : Y i j = 0 := by
  by_contra h0
  exact h (hY i j h0)
end Formalism.FourierDecayAlt.Q.QRR
