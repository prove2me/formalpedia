-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.pd_emb_1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:11:40.600844+00:00
-- url     : https://prove2.me/submissions/2e05aa59-e79f-4f01-bf60-242a7e59c867

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
    pd k (emb j k h) = emb j k (pd 1 h) := by
  rw [emb_apply, emb_apply, pd,
    Formalism.G.LogCR.pderiv_subst (fun s => by fin_cases s <;> simp) h k, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [MvPowerSeries.pderiv_X_self, MvPowerSeries.pderiv_X_of_ne hjk, mul_one, mul_zero,
    zero_add]
end Formalism.L2.Th1.B.Fs
