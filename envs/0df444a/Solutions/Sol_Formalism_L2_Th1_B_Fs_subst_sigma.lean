-- Prove2me | solution 1 for Formalism.L2.Th1.B.Fs.subst_sigma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:13:17.747698+00:00
-- url     : https://prove2.me/submissions/1a67d0e9-3aef-4231-9ee7-184910c4a255

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RealAdelicInertTransportTypeFormsEqAlt
import Theorems.Thm_Formalism_L2_Th1_B_Fs_psubst_fExp
import Theorems.Thm_Formalism_L2_Th1_B_Fs_sigS_cc
import Theorems.Thm_Formalism_L2_Th1_B_Add0_sigS_cc


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
theorem _root_.solution {ι : Type} (P : PowerSeries K) {u : MvPowerSeries ι K}
    (hu : MvPowerSeries.constantCoeff u = 0) :
    PowerSeries.subst u (sigma P) = u * fExp (PowerSeries.subst u (sigS P)) := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero hu
  rw [sigma, PowerSeries.subst_mul hs, PowerSeries.subst_X hs, psubst_fExp hu (sigS_cc P)]
end Formalism.L2.Th1.B.Fs
