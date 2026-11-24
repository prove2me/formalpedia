-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation.vAB_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:20:39.225559+00:00
-- url     : https://prove2.me/submissions/8b878aab-e713-473a-9d40-33a77212ad75

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonicShiftEvaluation_EvalXAddCMul
import Theorems.Thm_Formalism_FourierDecayAlt_Q_VMonicMonicShiftEvaluation_eval_X_add_C_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation
open Formalism.QuantumDeterminants
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation
theorem _root_.solution (r : ℕ) (Y : ℂ) (i : ℕ) (f : WSm r E) :
    (vAB r Y i).1 (f : (Fin r → ℂ) → E) = (((PQ r E i).1.eval (algebraMap ℂ (R r E) Y)) f : WSm r E) ∧
    (vAB r Y i).2 (f : (Fin r → ℂ) → E) = (((PQ r E i).2.eval (algebraMap ℂ (R r E) Y)) f : WSm r E) := by
  induction i generalizing f with
  | zero => simp [vAB, PQ]
  | succ i ih =>
    by_cases h : i < r
    · simp only [vAB, PQ, dif_pos h]
      refine ⟨?_, ?_⟩
      · rw [(ih f).1, (ih f).2, eval_sub, eval_X_add_C_mul, eval_C_mul]
        simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
          Module.algebraMap_end_apply, Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul]
        rfl
      · rw [(ih f).1, eval_C_mul]
        rfl
    · simp only [vAB, PQ, dif_neg h]
      exact ih f
end Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation
