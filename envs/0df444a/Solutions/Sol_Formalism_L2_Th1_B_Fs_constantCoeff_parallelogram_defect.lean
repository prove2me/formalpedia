-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.constantCoeff_parallelogram_defect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:10:39.909835+00:00
-- url     : https://prove2.me/submissions/a3240364-649e-422c-8f15-9062d67913ed

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
import Theorems.Thm_Formalism_L2_Th1_B_Fs_cc_psubst
import Theorems.Thm_Formalism_L2_Th1_B_Add1_cc_psubst


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
    MvPowerSeries.constantCoeff (par0 f) = 0 := by
  simp only [par0, atS, atD, at1, map_add, map_sub, map_mul]
  rw [cc_psubst (by simp) hf, cc_psubst (by simp) hf, cc_psubst (by simp) hf,
    cc_psubst (by simp) hf]
  simp
end Formalism.L2.Th1.B.Fs
