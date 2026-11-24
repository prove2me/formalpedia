-- Prove2me | solution 1 for Formalism.L2.Th1.B.Map.cc_sig1S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:21:19.6153+00:00
-- url     : https://prove2.me/submissions/9c4849fd-1229-4418-a4c9-caf6bc714e0f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_prim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Map
open Formalism.InvariantFactorPaths.G7 (at1 cob)
variable {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K'] (j : K →+* K')
namespace Formalism.L2.Th1.B.Map
theorem _root_.solution (e1 kap : K) (w : PowerSeries K) :
    PowerSeries.constantCoeff (sigmaOneSeries e1 kap w) = 0 := by
  unfold Formalism.L2.Th1.B.sigmaOneSeries
  rw [map_neg, Formalism.L2.Th1.B.constantCoeff_prim, neg_zero]
end Formalism.L2.Th1.B.Map
