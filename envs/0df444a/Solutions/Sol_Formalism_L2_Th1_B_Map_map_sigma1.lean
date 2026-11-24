-- Prove2me | solution 1 for Formalism.L2.Th1.B.Map.map_sigma1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:49:31.752448+00:00
-- url     : https://prove2.me/submissions/4a540362-051a-41a9-a058-67346d7fd5dd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Theorems.Thm_P2M_Formalism_L2_Th1_B_Map_map_fExp__32d85cf1f169
import Theorems.Thm_Formalism_L2_Th1_B_Map_map_sig1S
import Theorems.Thm_Formalism_L2_Th1_B_Map_cc_sig1S

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
    PowerSeries.map j (sigma1 e1 kap w) = sigma1 (j e1) (j kap) (PowerSeries.map j w) := by
  unfold Formalism.L2.Th1.B.sigma1
  rw [map_fExp' j (cc_sig1S e1 kap w), map_sig1S]
end Formalism.L2.Th1.B.Map
