-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.cb_anti_of_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:52:08.003849+00:00
-- url     : https://prove2.me/submissions/1d4c2634-e83e-450f-8f6d-db012271825c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_CbStrictMonoOfAnti
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


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
    ∀ i j, 1 ≤ i → i < j → j ≤ n → a j < a i := by
  intro i j hi hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases h : i < j
    · exact lt_trans (ha j (by omega) hj) (ih h (by omega))
    · have e : i = j := by omega
      rw [e]
      exact ha j (by omega) hj
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
