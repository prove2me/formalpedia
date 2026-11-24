-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.psubst_fExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:03:08.727665+00:00
-- url     : https://prove2.me/submissions/19304863-095c-4373-9d7a-75c6b20567b0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
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
theorem _root_.solution {ι : Type} {u : MvPowerSeries ι K} (hu : MvPowerSeries.constantCoeff u = 0)
    {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.subst u (fExp f) = fExp (PowerSeries.subst u f) :=
  Formalism.L2.Th1.B.subst_fExp (ι := Unit) (φ := fun _ => u) (fun _ => hu) hf
end Formalism.L2.Th1.B.Fs
