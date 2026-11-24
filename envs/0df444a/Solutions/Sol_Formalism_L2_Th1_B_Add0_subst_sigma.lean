-- Prove2me | solution 1 for Formalism.L2.Th1.B.Add0.subst_sigma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:20:15.11122+00:00
-- url     : https://prove2.me/submissions/d2f3167d-bc32-40c9-acfb-b5114d2d9375

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_PderivZeroZeroWeierstrassDifference
import Theorems.Thm_Formalism_L2_Th1_B_Add0_subst_fExp
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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
open Formalism.InvariantFactorPaths.G7 (at1)
open Add0
open Formalism.L2.Th1.B.Add0
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.Add0
theorem _root_.solution (h3 : ExpLogSubst) (P : PowerSeries K) {u : MvPowerSeries (Fin 2) K}
    (hu : MvPowerSeries.constantCoeff u = 0) :
    PowerSeries.subst u (sigma P) = u * fExp (PowerSeries.subst u (sigS P)) := by
  have ha : PowerSeries.HasSubst u := PowerSeries.HasSubst.of_constantCoeff_zero hu
  unfold sigma
  rw [← PowerSeries.coe_substAlgHom ha, map_mul, PowerSeries.coe_substAlgHom, PowerSeries.subst_X ha,
    subst_fExp h3 hu (sigS_cc P)]
end Formalism.L2.Th1.B.Add0
