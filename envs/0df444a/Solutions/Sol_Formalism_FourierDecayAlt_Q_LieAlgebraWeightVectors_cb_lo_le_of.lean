-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.cb_lo_le_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:52:13.521872+00:00
-- url     : https://prove2.me/submissions/6da7d0f1-86b1-4b17-89de-fa10aab28664

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_CbStrictMonoOfAnti
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


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
theorem _root_.solution (P : M.Par) (i : ℕ) (x : ℝ) (h1 : (Pp P).lo i ≤ x) (h2 : (Pq P).lo i ≤ x) :
    P.lo i ≤ x := by
  change max (P.u' (i + 1)) (P.u' (i + 1)) + 1 / 2 ≤ x at h1
  change max (P.u (i + 1)) (P.u (i + 1)) + 1 / 2 ≤ x at h2
  rw [max_self] at h1 h2
  show max (P.u (i + 1)) (P.u' (i + 1)) + 1 / 2 ≤ x
  have := max_le (show P.u (i + 1) ≤ x - 1 / 2 by linarith) (show P.u' (i + 1) ≤ x - 1 / 2 by linarith)
  linarith
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
