-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.cb_strictMono_of_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:12:41.264373+00:00
-- url     : https://prove2.me/submissions/749b50da-3424-4742-8898-b022cb0cec87

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_CbStrictMonoOfAnti
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_anti_of_succ

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
theorem _root_.solution {n : ℕ} {a : ℕ → ℝ} (ha : ∀ i, 1 ≤ i → i + 1 ≤ n → a (i + 1) < a i) :
    StrictMono (fun j : Fin n => -a (j.1 + 1)) := by
  intro i j hij
  have h' : i.val < j.val := hij
  have hjn := j.isLt
  have := cb_anti_of_succ ha (i.val + 1) (j.val + 1) (by omega) (by omega) (by omega)
  show -a (i.val + 1) < -a (j.val + 1)
  linarith
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
