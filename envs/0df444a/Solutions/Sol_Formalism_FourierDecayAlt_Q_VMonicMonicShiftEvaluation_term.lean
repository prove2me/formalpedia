-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation.term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:06:13.550408+00:00
-- url     : https://prove2.me/submissions/307847d6-8f22-4a95-8f57-9904abbf9301

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonicShiftEvaluation_EvalXAddCMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonicShiftEvaluation_CapelliPolynomialMonic

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
theorem _root_.solution (r : ℕ) (c : R r E) (Y : ℂ) (j : ℕ) (f : WSm r E) :
    (((c * algebraMap ℂ (R r E) Y ^ j) f : WSm r E) : (Fin r → ℂ) → E) =
      Y ^ j • ((c f : WSm r E) : (Fin r → ℂ) → E) := by
  rw [← map_pow, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul, Submodule.coe_smul]
end Formalism.FourierDecayAlt.Q.VMonicMonicShiftEvaluation
