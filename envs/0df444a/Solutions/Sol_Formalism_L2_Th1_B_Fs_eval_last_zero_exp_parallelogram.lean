-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.eval_last_zero_exp_parallelogram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:32:54.105363+00:00
-- url     : https://prove2.me/submissions/5914e355-af06-42ee-90a7-3cfecf57e902

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
import Theorems.Thm_Formalism_L2_Th1_B_Fs_embed_pair_at_variable_zero
import Theorems.Thm_Formalism_L2_Th1_B_Fs_embed_pair_at_variable_one
import Theorems.Thm_Formalism_L2_Th1_B_Fs_emb_atD
import Theorems.Thm_Formalism_L2_Th1_B_Fs_emb_atS
import Theorems.Thm_Formalism_L2_Th1_B_Fs_eval_last_zero_X_zero
import Theorems.Thm_Formalism_L2_Th1_B_Fs_eval_last_zero_X_one
import Theorems.Thm_Formalism_L2_Th1_B_Fs_eval_last_zero_X_two
import Theorems.Thm_Formalism_L2_Th1_B_Fs_eval_last_zero_subst_series
import Theorems.Thm_Formalism_L2_Th1_B_Fs_eval_last_zero_at_variable_zero
import Theorems.Thm_Formalism_L2_Th1_B_Fs_eval_last_zero_at_variable_one

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
theorem _root_.solution {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    ev3H (fsE f) = emb 0 1 (par0 f) := by
  have h0 : PowerSeries.subst (0 : A3) f = 0 := PowerSeries.subst_zero_of_constantCoeff_zero hf
  simp only [fsE, par0, evalSumThree, evalDiffThree, map_add, map_sub, map_mul, map_ofNat, emb_atS, emb_atD,
    embed_pair_at_variable_zero, embed_pair_at_variable_one]
  rw [eval_last_zero_subst_series f (by simp), eval_last_zero_subst_series f (by simp), eval_last_zero_subst_series f (by simp),
    eval_last_zero_subst_series f (by simp), eval_last_zero_at_variable_zero, eval_last_zero_at_variable_one, at1, at1, at1, eval_last_zero_subst_series f (by simp)]
  simp only [map_add, map_sub, eval_last_zero_X_zero, eval_last_zero_X_one, eval_last_zero_X_two, add_zero, sub_zero, h0]
  ring
end Formalism.L2.Th1.B.Fs
