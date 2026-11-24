-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.emb_fExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:11:37.625797+00:00
-- url     : https://prove2.me/submissions/86653c81-c1ab-437b-83ed-320f1c4c382e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
import Theorems.Thm_Formalism_L2_Th1_B_Fs_emb_apply
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
theorem _root_.solution (j k : Fin 3) {f : MvPowerSeries (Fin 2) K}
    (hf : MvPowerSeries.constantCoeff f = 0) : emb j k (fExp f) = fExp (emb j k f) := by
  rw [emb_apply, emb_apply]
  exact Formalism.L2.Th1.B.subst_fExp (fun s => by fin_cases s <;> simp) hf
end Formalism.L2.Th1.B.Fs
