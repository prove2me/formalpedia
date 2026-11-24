-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.cb_le_hi_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:49:02.126826+00:00
-- url     : https://prove2.me/submissions/f515eec0-5879-435c-90b0-3c1cfb1f3895

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
theorem _root_.solution (P : M.Par) (i : ℕ) (x : ℝ) (h1 : x ≤ (Pp P).hi i) (h2 : x ≤ (Pq P).hi i) :
    x ≤ P.hi i := by
  change x ≤ min (P.u' i) (P.u' i) - 1 / 2 at h1
  change x ≤ min (P.u i) (P.u i) - 1 / 2 at h2
  rw [min_self] at h1 h2
  show x ≤ min (P.u i) (P.u' i) - 1 / 2
  have := le_min (show x + 1 / 2 ≤ P.u i by linarith) (show x + 1 / 2 ≤ P.u' i by linarith)
  linarith
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
