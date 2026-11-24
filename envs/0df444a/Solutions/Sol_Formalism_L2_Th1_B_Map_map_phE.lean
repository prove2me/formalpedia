-- Prove2me | solution 1 for Formalism.L2.Th1.B.Map.map_phE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:21:15.449213+00:00
-- url     : https://prove2.me/submissions/d0e62578-6f34-4088-b51e-ea5b103d42ef

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Theorems.Thm_P2M_Formalism_L2_Th1_B_Map_map_psubst__d587dd5fe1df
import Theorems.Thm_Formalism_L2_Th1_B_Map_map_sig1S

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
theorem _root_.solution (s2 e1 kap : K) (w : PowerSeries K) {l : PowerSeries K}
    (h0 : PowerSeries.constantCoeff l = 0) :
    PowerSeries.map j (phE s2 e1 kap w l) =
      phE (j s2) (j e1) (j kap) (PowerSeries.map j w) (PowerSeries.map j l) := by
  unfold Formalism.L2.Th1.B.phE
  rw [map_add, map_neg, map_psubst' j h0, map_sig1S, map_mul,
    PowerSeries.map_C, map_div₀, map_ofNat, map_pow]
end Formalism.L2.Th1.B.Map
