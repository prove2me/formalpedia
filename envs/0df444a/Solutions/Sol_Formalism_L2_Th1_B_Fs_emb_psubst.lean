-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.emb_psubst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:11:55.097995+00:00
-- url     : https://prove2.me/submissions/60b7a3c8-c324-4748-9afc-0047f3c1d1d7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
import Theorems.Thm_Formalism_L2_Th1_B_Fs_emb_apply
import Theorems.Thm_Formalism_L2_Th1_B_psubst_msubst


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
theorem _root_.solution (j k : Fin 3) (f : PowerSeries K) {u : MvPowerSeries (Fin 2) K}
    (hu : MvPowerSeries.constantCoeff u = 0) :
    emb j k (PowerSeries.subst u f) = PowerSeries.subst (emb j k u) f := by
  rw [emb_apply, emb_apply, psubst_msubst f hu (hs_emb j k)]
end Formalism.L2.Th1.B.Fs
