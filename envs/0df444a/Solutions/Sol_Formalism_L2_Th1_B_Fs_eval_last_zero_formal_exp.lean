-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.eval_last_zero_formal_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:10:29.325974+00:00
-- url     : https://prove2.me/submissions/e6a20a95-a363-4b63-bc97-cb40d63d3484

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
import Theorems.Thm_Formalism_L2_Th1_B_Fs_eval_three_eq_eval_last_zero
import Theorems.Thm_Formalism_L2_Th1_B_Add0_subst_fExp
import Theorems.Thm_Formalism_L2_Th1_B_subst_fExp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Fs
open Formalism.InvariantFactorPaths.G7 (at1)
variable {K : Type} [Field K] [CharZero K]
local notation "A3" => MvPowerSeries (Fin 3) K
namespace Formalism.L2.Th1.B.Fs
theorem _root_.solution {f : A3} (hf : MvPowerSeries.constantCoeff f = 0) :
    ev3H (fExp f) = fExp (ev3H f) := by
  rw [← eval_three_eq_eval_last_zero, ← eval_three_eq_eval_last_zero]
  exact Formalism.L2.Th1.B.subst_fExp (fun s => by fin_cases s <;> simp) hf
end Formalism.L2.Th1.B.Fs
