-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.cb_lo_Pp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:52:11.607543+00:00
-- url     : https://prove2.me/submissions/c6fdec50-c52f-4bf7-aef4-51cfd839a19d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_CbStrictMonoOfAnti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution (P : M.Par) (i : ℕ) : (Pp P).lo i ≤ P.lo i := by
  show max (P.u' (i + 1)) (P.u' (i + 1)) + 1 / 2 ≤ max (P.u (i + 1)) (P.u' (i + 1)) + 1 / 2
  rw [max_self]
  linarith [le_max_right (P.u (i + 1)) (P.u' (i + 1))]
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
