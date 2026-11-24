-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.emb_cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:11:36.059904+00:00
-- url     : https://prove2.me/submissions/3b46340d-53d4-4ea0-8179-663da1a60913

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
import Theorems.Thm_Formalism_L2_Th1_B_Fs_emb_apply

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
theorem _root_.solution (j k : Fin 3) {h : MvPowerSeries (Fin 2) K}
    (hh : MvPowerSeries.constantCoeff h = 0) : MvPowerSeries.constantCoeff (emb j k h) = 0 := by
  rw [emb_apply]
  exact MvPowerSeries.constantCoeff_subst_eq_zero (hs_emb j k)
    (fun s => by fin_cases s <;> simp) hh
end Formalism.L2.Th1.B.Fs
