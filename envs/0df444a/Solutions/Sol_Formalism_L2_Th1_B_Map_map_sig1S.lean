-- Prove2me | solution 1 for Formalism.L2.Th1.B.Map.map_sig1S
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:50.720901+00:00
-- url     : https://prove2.me/submissions/bc9bfbd9-00ba-4cb6-9fef-e5acb6a82803

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Theorems.Thm_Formalism_L2_Th1_B_Map_map_prim

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
    PowerSeries.map j (sigmaOneSeries e1 kap w) = sigmaOneSeries (j e1) (j kap) (PowerSeries.map j w) := by
  unfold Formalism.L2.Th1.B.sigmaOneSeries
  rw [map_neg, map_prim, map_prim, map_add, map_mul, PowerSeries.map_C,
    PowerSeries.map_C]
end Formalism.L2.Th1.B.Map
