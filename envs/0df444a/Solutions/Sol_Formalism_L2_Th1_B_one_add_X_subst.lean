-- Prove2me | solution 1 for Formalism.L2.Th1.B.one_add_X_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:46.315+00:00
-- url     : https://prove2.me/submissions/e3c4f9a8-3ae3-43df-8b41-4ba26fc13cbd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst

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
open PowerSeries
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B
theorem _root_.solution {ι : Type} {a : MvPowerSeries ι K} (ha : HasSubst a) :
    (1 + X : PowerSeries K).subst a = 1 + a := by
  rw [← coe_substAlgHom ha, map_add, map_one, coe_substAlgHom, subst_X ha]
end Formalism.L2.Th1.B
