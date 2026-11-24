-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation.eval_X_add_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:56:39.99369+00:00
-- url     : https://prove2.me/submissions/163e8ca6-264b-4613-a83c-333c297c2062

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonicShiftEvaluation_EvalXAddCMul

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
theorem _root_.solution (r : ℕ) (P : (R r E)[X]) (q : R r E) (Y : ℂ) :
    ((X + C q) * P).eval (algebraMap ℂ (R r E) Y) =
      algebraMap ℂ (R r E) Y * P.eval (algebraMap ℂ (R r E) Y) + q * P.eval (algebraMap ℂ (R r E) Y) := by
  rw [add_mul, eval_add, eval_C_mul, (commute_X P).eq, eval_mul_X, Algebra.commutes]
end Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation
