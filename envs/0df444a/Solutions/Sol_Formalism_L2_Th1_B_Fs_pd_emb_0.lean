-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.pd_emb_0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:11:38.990398+00:00
-- url     : https://prove2.me/submissions/6aa60017-b506-4282-b41c-267caddf3809

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
import Theorems.Thm_Formalism_L2_Th1_B_Fs_emb_apply
import Theorems.Thm_Formalism_G_LogCR_pderiv_subst


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
theorem _root_.solution {j k : Fin 3} (hjk : j ≠ k) (h : MvPowerSeries (Fin 2) K) :
    pd j (emb j k h) = emb j k (pd 0 h) := by
  rw [emb_apply, emb_apply, pd,
    Formalism.G.LogCR.pderiv_subst (fun s => by fin_cases s <;> simp) h j, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [MvPowerSeries.pderiv_X_self, MvPowerSeries.pderiv_X_of_ne hjk.symm, mul_one, mul_zero,
    add_zero]
end Formalism.L2.Th1.B.Fs
