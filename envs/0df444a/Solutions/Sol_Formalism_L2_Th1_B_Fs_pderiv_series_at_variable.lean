-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.pderiv_series_at_variable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:14:36.100795+00:00
-- url     : https://prove2.me/submissions/4686d711-f776-4626-9f3e-165607695a83

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
import Theorems.Thm_Formalism_L2_Th1_B_Fs_pd_psubst
import Theorems.Thm_Formalism_L2_Th1_B_Fs_pdX

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
theorem _root_.solution (i j : Fin 3) (f : PowerSeries K) :
    MvPowerSeries.pderiv K i (at1 j f : A3) = at1 j (dz f) * if j = i then 1 else 0 := by
  rw [← pdX]; exact pd_psubst i (by simp) f
end Formalism.L2.Th1.B.Fs
